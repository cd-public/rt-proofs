Require Import Vbase ScheduleDefs BertognaResponseTimeDefsEDF divround helper
               ssreflect ssrbool eqtype ssrnat seq fintype bigop div path tuple.

Module ResponseTimeIterationEDF.

  Import Schedule ResponseTimeAnalysisEDF.

  Section Analysis.
    
    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> nat.
    Variable task_period: sporadic_task -> nat.
    Variable task_deadline: sporadic_task -> nat.
    
    Let task_with_response_time := (sporadic_task * nat)%type.
    
    Context {Job: eqType}.
    Variable job_cost: Job -> nat.
    Variable job_deadline: Job -> nat.
    Variable job_task: Job -> sporadic_task.

    Variable num_cpus: nat.

    (* Next we define the fixed-point iteration for computing
       Bertogna's response-time bound for any task in ts. *)
    
    (*Computation of EDF on list of pairs (T,R)*)
    
    Let max_steps (ts: taskset_of sporadic_task) :=
      \sum_(tsk <- ts) task_deadline tsk.

    Let I (rt_bounds: seq task_with_response_time)
          (tsk: sporadic_task) (delta: time) :=
      total_interference_bound_edf task_cost task_period task_deadline tsk rt_bounds delta.
    
    Let response_time_bound (rt_bounds: seq task_with_response_time)
                            (tsk: sporadic_task) (delta: time) :=
      task_cost tsk + div_floor (I rt_bounds tsk delta) num_cpus.
    
    Let initial_state (ts: taskset_of sporadic_task) :=
      map (fun t => (t, task_cost t)) ts.

    Definition update_bound (rt_bounds: seq task_with_response_time)
                        (pair : task_with_response_time) :=
      let (tsk, R) := pair in
        (tsk, response_time_bound rt_bounds tsk R).

    Definition edf_rta_iteration (rt_bounds: seq task_with_response_time) :=
      map (update_bound rt_bounds) rt_bounds.

    Definition R_le_deadline (pair: task_with_response_time) :=
      let (tsk, R) := pair in
        R <= task_deadline tsk.
    
    Definition R_list_edf (ts: taskset_of sporadic_task) :=
      let R_values := iter (max_steps ts) edf_rta_iteration (initial_state ts) in
        if (all R_le_deadline R_values) then
          Some R_values
        else None.
    
    (* The schedulability test simply checks if we got a list of
       response-time bounds (i.e., if the computation did not fail). *)
    Definition edf_schedulable (ts: taskset_of sporadic_task) :=
      R_list_edf ts != None.
    
    Section AuxiliaryLemmas.

    End AuxiliaryLemmas.
    
    Section Proof.

      (* Consider a task set ts. *)
      Variable ts: taskset_of sporadic_task.
      
      (* Assume the task set has no duplicates, ... *)
      Hypothesis H_ts_is_a_set: uniq ts.

      (* ...all tasks have valid parameters, ... *)
      Hypothesis H_valid_task_parameters:
        valid_sporadic_taskset task_cost task_period task_deadline ts.

      (* ...restricted deadlines, ...*)
      Hypothesis H_restricted_deadlines:
        forall tsk, tsk \in ts -> task_deadline tsk <= task_period tsk.

      (* ...and tasks are ordered by increasing priorities. *)
      (*Hypothesis H_sorted_ts: sorted EDF ts.*)

      (* Next, consider any arrival sequence such that...*)
      Context {arr_seq: arrival_sequence Job}.

     (* ...all jobs come from task set ts, ...*)
      Hypothesis H_all_jobs_from_taskset:
        forall (j: JobIn arr_seq), job_task j \in ts.
      
      (* ...they have valid parameters,...*)
      Hypothesis H_valid_job_parameters:
        forall (j: JobIn arr_seq),
          valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j.
      
      (* ... and satisfy the sporadic task model.*)
      Hypothesis H_sporadic_tasks:
        sporadic_task_model task_period arr_seq job_task.
      
      (* Then, consider any platform with at least one CPU and unit
         unit execution rate, where...*)
      Variable rate: Job -> processor num_cpus -> nat.
      Variable sched: schedule num_cpus arr_seq.
      Hypothesis H_at_least_one_cpu :
        num_cpus > 0.
      Hypothesis H_rate_equals_one :
        forall j cpu, rate j cpu = 1.

      (* ...jobs only execute after they arrived and no longer
         than their execution costs,... *)
      Hypothesis H_jobs_must_arrive_to_execute:
        jobs_must_arrive_to_execute sched.
      Hypothesis H_completed_jobs_dont_execute:
        completed_jobs_dont_execute job_cost rate sched.

      (* ...and do not execute in parallel. *)
      Hypothesis H_no_parallelism:
        jobs_dont_execute_in_parallel sched.

      (* Assume the platform satisfies the global scheduling invariant. *)
      Hypothesis H_global_scheduling_invariant:
        forall (tsk: sporadic_task) (j: JobIn arr_seq) (t: time),
          tsk \in ts ->
          job_task j = tsk ->
          backlogged job_cost rate sched j t ->
          count
            (fun tsk_other : _ =>
               is_interfering_task_jlfp tsk tsk_other &&
               task_is_scheduled job_task sched tsk_other t) ts = num_cpus.

      Definition no_deadline_missed_by_task (tsk: sporadic_task) :=
        task_misses_no_deadline job_cost job_deadline job_task rate sched tsk.
      Definition no_deadline_missed_by_job :=
        job_misses_no_deadline job_cost job_deadline rate sched.

      Section HelperLemma.

        Lemma R_list_converges_helper :
          forall rt_bounds,
            R_list_edf ts = Some rt_bounds ->
            valid_sporadic_taskset task_cost task_period task_deadline ts ->
            iter (max_steps ts) edf_rta_iteration (initial_state ts)
              = iter (max_steps ts).+1 edf_rta_iteration (initial_state ts).
        Proof.
          intros rt_bounds SOME VALID.
          unfold R_list_edf in SOME; desf.

          set f := fun x => iter x edf_rta_iteration (initial_state ts).
          fold (f (max_steps ts)) in *; fold (f (max_steps ts).+1).

          set all_le := fun (v1 v2: list task_with_response_time) =>
             all (fun p => (snd (fst p)) <= (snd (snd p))) (zip v1 v2).

          set one_lt := fun (v1 v2: list task_with_response_time) =>
             has (fun p => (snd (fst p)) < (snd (snd p))) (zip v1 v2).

          assert (REFL: reflexive all_le).
          {
            intros l; unfold all_le.
            destruct l; first by done.
            apply/(zipP (fun x y => snd x <= snd y)); try (by ins).
            by ins; apply leqnn.
          }

          assert (TRANS: transitive all_le).
          {
            unfold transitive, all_le; intros y x z LExy LEyz.
            move: LExy LEyz => /allP LExy /allP LEyz; apply/allP.
            
            admit. (* Weird cannot prove this! *)
          }

          assert (INIT: all_le (initial_state ts)
                               (edf_rta_iteration (initial_state ts))).
          {
            unfold all_le.
            exploit (@size1_zip _ _ (initial_state ts) (edf_rta_iteration (initial_state ts)));
              [by rewrite 3!size_map | intro SIZE1].
            destruct ts as [| tsk ts']; first by done.
            apply/(zipP (fun x y => snd x <= snd y));
              [by done | by rewrite 3!size_map |].
            {
              unfold initial_state in *; intros i LTi.
              rewrite (nth_map tsk) /=;
                last by rewrite /= size_map in SIZE1; rewrite -SIZE1.
              rewrite (nth_map (tsk,num_cpus)); unfold update_bound;
                last by simpl in *; rewrite -SIZE1.
              desf; simpl; unfold response_time_bound.
              assert (EQtsk: nth tsk (tsk :: ts') i = s).
              {
                admit. (* Should be provable *)
              }
              by rewrite EQtsk leq_addr.
            }
          }

          assert (MON:forall x1 x2,
                     all_le x1 x2 ->
                     all_le (edf_rta_iteration x1) (edf_rta_iteration x2)).
          {
            intros x1 x2 LE.
            move: LE => /(zipP (fun x y => snd x <= snd y)) LE.
            apply/(zipP (fun x y => snd x <= snd y)). admit.
          }
            
          assert (GROWS: forall k, all_le (f k) (f k.+1)).
          {
            intros k.
            apply fun_mon_iter_mon_generic with (x1 := k) (x2 := k.+1);
              try (by ins); by apply leqnSn.
          }
          
          (* Either f converges by the deadline or not. *)
          unfold max_steps in *.
          set sum_d := \sum_(tsk <- ts) task_deadline tsk.
          destruct ([exists k in 'I_(sum_d), f k == f k.+1]) eqn:EX.
          {
            move: EX => /exists_inP EX; destruct EX as [k _ ITERk].
            move: ITERk => /eqP ITERk.
            apply iter_fix with (k := k);
              [by ins | by apply ltnW, ltn_ord].
          }
          
          apply negbT in EX; rewrite negb_exists_in in EX.
          move: EX => /forall_inP EX.

          assert (GT: forall k: 'I_(sum_d), one_lt (f k) (f k.+1)).
          {
            intros step; unfold one_lt.
            rewrite -[has _ _]negbK; apply/negP; unfold not; intro ALL.
            rewrite -all_predC in ALL.
            move: ALL => /allP ALL.
            exploit (EX step); [by done | intro DIFF].
            assert (DUMMY: exists tsk: sporadic_task, True).
            {
              unfold f, edf_rta_iteration, initial_state in DIFF.
              induction ts as [| tsk0 ts']; last by exists tsk0.
              simpl in DIFF.
              clear ALL EX MON VALID DIFF.
              destruct step as [step LT].
              by unfold sum_d in LT; rewrite big_nil in LT.
            }
            des; clear DUMMY.
            move: DIFF => /eqP DIFF; apply DIFF.
            apply eq_from_nth with (x0 := (tsk, 0));
              first by simpl; rewrite size_map.
            {
              intros i LTi.
              remember (nth (tsk, 0)(f step) i) as p_i;rewrite -Heqp_i.
              remember (nth (tsk, 0)(f step.+1) i) as p_i';rewrite -Heqp_i'.
              rename Heqp_i into EQ, Heqp_i' into EQ'.
              exploit (ALL (p_i, p_i')).
              {
                rewrite EQ EQ'.
                rewrite -nth_zip; last by unfold f; rewrite iterS size_map.
                apply mem_nth; rewrite size_zip.
                unfold f; rewrite iterS size_map.
                by rewrite minnn.
              }
              unfold predC; simpl; rewrite -ltnNge; intro LTp.
              
              specialize (GROWS step).
              move: GROWS => /allP GROWS.
              exploit (GROWS (p_i, p_i')).
              {
                rewrite EQ EQ'.
                rewrite -nth_zip; last by unfold f; rewrite iterS size_map.
                apply mem_nth; rewrite size_zip.
                unfold f; rewrite iterS size_map.
                by rewrite minnn.
              }
              simpl; intros LE.

              destruct p_i as [tsk_i R_i], p_i' as [tsk_i' R_i'].
              simpl in *.
              assert (EQtsk: tsk_i = tsk_i').
              {
                unfold edf_rta_iteration in EQ'.
                rewrite (nth_map (tsk, 0)) in EQ'; last by done.
                by unfold update_bound in EQ'; desf.
              }
              rewrite EQtsk; f_equal.
              by apply/eqP; rewrite eqn_leq; apply/andP; split.
            }
          }
          
          assert (EXCEEDS: forall step: 'I_(sum_d),
                             \sum_(p <- f step) snd p > step).
          {
            intro step; destruct step as [step LT].
            induction step.
            {
              apply leq_ltn_trans with (n := \sum_(p <- initial_state ts) 0);               first by rewrite big_const_seq iter_addn mul0n addn0.
              apply leq_trans with (n := \sum_(p <- initial_state ts) 1).
              {
                rewrite 2!big_const_seq 2!iter_addn mul0n mul1n 2!addn0.
                destruct ts; last by done.
                
                by unfold sum_d in LT; rewrite big_nil in LT.
              }
              rewrite big_seq_cond [\sum_(p <- _ | true) _]big_seq_cond.
              apply leq_sum.
              intro p; rewrite andbT; simpl; intros IN.
              destruct p as [tsk R]; simpl in *.
              move: IN => /mapP IN; destruct IN as [x IN SUBST].
              inversion SUBST; subst; clear SUBST.
              exploit (VALID x); first by done.
              unfold valid_sporadic_taskset, is_valid_sporadic_task.
              by unfold task_deadline_positive; ins; des.
            }
            {
              assert (LT': step < sum_d).
                by apply leq_ltn_trans with (n := step.+1).
              simpl in *; exploit IHstep; [by done | intro LE].
              specialize (GT (Ordinal LT')).
              simpl in *; clear LT LT' IHstep.
              move: GT => /hasP GT; destruct GT as [p IN LTpair].
              apply leq_trans with (n := (\sum_(p <- f step) snd p) + 1);
                first by rewrite addn1 ltnS.
              destruct p as [p p']; simpl in *.

              rewrite (big_nth p) (big_nth p).
              set idx := index (p,p') (zip (f step) (edf_rta_iteration (f step))).
              rewrite -> big_cat_nat with (n := idx);
                [simpl | by done |]; last first.
              {
                apply leq_trans with (n := size (zip (f step)
                                        (edf_rta_iteration (f step))));
                first by apply index_size.
                by rewrite size_zip size_map minnn.
              }
              rewrite -> big_cat_nat with (n := idx)
                                 (p := size (edf_rta_iteration (f step)));
                [simpl | by done |]; last first.
              {
                apply leq_trans with (n := size (zip (f step)
                                        (edf_rta_iteration (f step))));
                first by apply index_size. 
                by rewrite size_zip size_map minnn.
              }
              specialize (GROWS step); unfold all_le in GROWS.
              move: GROWS => /(zipP (fun x y => snd x <= snd y)) GROWS.
              rewrite -addnA; apply leq_add.
              {
                rewrite big_nat_cond
                        [\sum_(_ <= _ < _ | true) _]big_nat_cond.
                apply leq_sum; intro i; rewrite andbT.
                move => /andP [_ LT].                
                apply GROWS; first by rewrite size_map.
                by apply (leq_trans LT), index_size.
              }
              {
                rewrite size_map.
                destruct (size (f step)) eqn:SIZE.
                {
                  rewrite SIZE; apply size0nil in SIZE.
                  by rewrite SIZE big_nil in LE.
                } rewrite SIZE.
                assert (LEidx: idx <= n).
                {
                  unfold idx; rewrite -ltnS -SIZE.
                  rewrite -(@size1_zip _ _ _ (edf_rta_iteration (f step)));
                    last by rewrite size_map leqnn.
                  by rewrite index_mem.
                }
                rewrite 2?big_nat_recl //.
                rewrite -addnA [_ + 1]addnC addnA.
                apply leq_add; last first.
                {
                  rewrite big_nat_cond
                          [\sum_(_ <= _ < _ | true) _]big_nat_cond.
                  apply leq_sum; intro i; rewrite andbT.
                  move => /andP [_ LT].
                  apply GROWS; first by rewrite size_map.
                  apply leq_ltn_trans with (n := n); first by done.
                  apply leq_trans with (n := size (f step));
                    first by rewrite -SIZE.
                  rewrite -(@size1_zip _ _ _ (edf_rta_iteration (f step)));
                    [by done | by rewrite size_map leqnn].
                }
                {
                  rewrite addn1.
                  have NTH := @nth_index _ (p,p) (p,p') (zip (f step) (edf_rta_iteration (f step))) IN.
                  rewrite nth_zip in NTH; last by rewrite size_map.
                  inversion NTH.
                  rewrite H1; rewrite H0 in H1; rewrite H0.
                  by rewrite H0 H1.
                }
              }
            }
          }
          admit.
        Qed.
        
        Lemma R_list_converges :
          forall tsk R rt_bounds,
            R_list_edf ts = Some rt_bounds ->
            (tsk, R) \in rt_bounds ->
            R = task_cost tsk + div_floor (I rt_bounds tsk R) num_cpus.
        Proof.
          intros tsk R rt_bounds SOME IN.
          unfold R_list_edf in SOME; desf.

          f 
          set (f x := task_cost tsk + div_floor (I (iter x edf_rta_iteration (initial_state ts)) tsk R) num_cpus).
          fold (f (max_steps ts)).

          
        (* First prove that f is monotonic.*)
        assert (MON: forall x1 x2, x1 <= x2 -> f x1 <= f x2).
        {
          intros x1 x2 LEx; unfold f, per_task_rta.
          apply fun_mon_iter_mon; [by ins | by ins; apply leq_addr |].
          clear LEx x1 x2; intros x1 x2 LEx.
          
          unfold div_floor, total_interference_bound_fp.
          rewrite big_seq_cond [\sum_(i <- _ | let '(tsk_other, _) := i in
                                   _ && (tsk_other != tsk))_]big_seq_cond.
          rewrite leq_add2l leq_div2r // leq_sum //.

          intros i; destruct (i \in rt_bounds) eqn:HP;
            last by rewrite andFb.
          destruct i as [i R]; intros _.
          have GE_COST := (R_list_ge_cost ts' rt_bounds i R).
          have INts := (R_list_non_empty ts' rt_bounds i SOME).
          destruct INts as [_ EX]; exploit EX; [by exists R | intro IN].
          unfold interference_bound; simpl.
          rewrite leq_min; apply/andP; split.
          {
            apply leq_trans with (n := W task_cost task_period i R x1); 
              first by apply geq_minl.            
            specialize (VALID i IN); des.
            by apply W_monotonic; try (by ins); apply GE_COST.          
          }
          {
            apply leq_trans with (n := x1 - task_cost tsk + 1);
              first by apply geq_minr.
            by rewrite leq_add2r leq_sub2r //.
          }
        }

          
          admit.
        Qed.

        (* The following lemma states that the response-time bounds
           computed using R_list are valid. *)
        Lemma R_list_ge_cost :
          forall rt_bounds tsk R,
            R_list_edf ts = Some rt_bounds ->
            (tsk, R) \in rt_bounds ->
            R >= task_cost tsk.
        Proof.
          intros rt_bounds tsk R SOME PAIR.
          unfold R_list_edf in SOME.
          destruct (all R_le_deadline (iter (max_steps ts) edf_rta_iteration (initial_state ts)));
            last by ins.
          inversion SOME as [EQ]; clear SOME; subst.
          generalize dependent R.
          induction (max_steps ts) as [| step]; simpl in *.
          {
            intros R IN; unfold initial_state in IN.
            move: IN => /mapP IN; destruct IN as [tsk' IN EQ]; inversion EQ; subst.
            by apply leqnn.
          }
          {
            intros R IN.
            set prev_state := iter step edf_rta_iteration (initial_state ts).
            fold prev_state in IN, IHstep.
            unfold edf_rta_iteration at 1 in IN.
            move: IN => /mapP IN; destruct IN as [(tsk',R') IN EQ].
            inversion EQ as [[xxx EQ']]; subst.
            by apply leq_addr.
          }      
        Qed.
        
        Lemma R_list_le_deadline :
          forall rt_bounds tsk R,
            R_list_edf ts = Some rt_bounds ->
            (tsk, R) \in rt_bounds ->
            R <= task_deadline tsk.
        Proof.
          intros rt_bounds tsk R SOME PAIR; unfold R_list_edf in SOME.
          destruct (all R_le_deadline (iter (max_steps ts)
                                            edf_rta_iteration (initial_state ts))) eqn:DEADLINE;
            last by done.
          move: DEADLINE => /allP DEADLINE.
          inversion SOME as [EQ]; rewrite -EQ in PAIR.
          by specialize (DEADLINE (tsk, R) PAIR).
        Qed.

        Lemma R_list_has_R_for_every_tsk :
          forall rt_bounds tsk,
            R_list_edf ts = Some rt_bounds ->
            tsk \in ts ->
            exists R,
              (tsk, R) \in rt_bounds.
        Proof.
          intros rt_bounds tsk SOME IN.
          unfold R_list_edf in SOME.
          destruct (all R_le_deadline (iter (max_steps ts) edf_rta_iteration (initial_state ts)));
            last by done.
          inversion SOME as [EQ]; clear SOME EQ.
          generalize dependent tsk.
          induction (max_steps ts) as [| step]; simpl in *.
          {
            intros tsk IN; unfold initial_state.
            exists (task_cost tsk).
            by apply/mapP; exists tsk.
          }
          {
            intros tsk IN.
            set prev_state := iter step edf_rta_iteration (initial_state ts).
            fold prev_state in IN, IHstep.
            specialize (IHstep tsk IN); des.
            exists (response_time_bound prev_state tsk R).
            by apply/mapP; exists (tsk, R); [by done | by f_equal].
          }
        Qed.
        
        Lemma R_list_has_response_time_bounds :
          forall rt_bounds tsk R,
            R_list_edf ts = Some rt_bounds ->
            (tsk, R) \in rt_bounds ->
            forall j : JobIn arr_seq,
              job_task j = tsk ->
              completed job_cost rate sched j (job_arrival j + R).
        Proof.
          intros rt_bounds tsk R SOME IN j JOBj.
          unfold edf_rta_iteration in *.
          have BOUND := bertogna_cirinei_response_time_bound_edf.
          unfold is_response_time_bound_of_task, job_has_completed_by in *.
          apply BOUND with (task_cost := task_cost) (task_period := task_period)
             (task_deadline := task_deadline) (job_deadline := job_deadline)
             (job_task := job_task) (ts := ts) (tsk := tsk) (rt_bounds := rt_bounds); try (by ins).
            by ins; apply R_list_converges.
            by ins; apply R_list_ge_cost with (rt_bounds := rt_bounds).
            by ins; apply R_list_le_deadline with (rt_bounds := rt_bounds).
        Qed.

      End HelperLemma.
      
      (* If the schedulability test suceeds, ...*)
      Hypothesis H_test_succeeds: edf_schedulable ts.
      
      (*..., then no task misses its deadline,... *)
      Theorem taskset_schedulable_by_fp_rta :
        forall tsk, tsk \in ts -> no_deadline_missed_by_task tsk.
      Proof.
        unfold no_deadline_missed_by_task, task_misses_no_deadline,
               job_misses_no_deadline, completed,
               edf_schedulable,
               valid_sporadic_job in *.
        rename H_valid_job_parameters into JOBPARAMS,
               H_valid_task_parameters into TASKPARAMS,
               H_restricted_deadlines into RESTR,
               H_completed_jobs_dont_execute into COMP,
               H_jobs_must_arrive_to_execute into MUSTARRIVE,
               H_global_scheduling_invariant into INVARIANT,
               H_all_jobs_from_taskset into ALLJOBS,
               H_test_succeeds into TEST.
        
        move => tsk INtsk j /eqP JOBtsk.
        have RLIST := (R_list_has_response_time_bounds).
        have DL := (R_list_le_deadline).
        have HAS := (R_list_has_R_for_every_tsk).
        
        destruct (R_list_edf ts) as [rt_bounds |]; last by ins.
        exploit (HAS rt_bounds tsk); [by ins | by ins | clear HAS; intro HAS; des].
        exploit (RLIST rt_bounds tsk R); [by ins | by ins | by apply JOBtsk | intro COMPLETED ].
        exploit (DL rt_bounds tsk R); [by ins | by ins | clear DL; intro DL].
   
        rewrite eqn_leq; apply/andP; split; first by apply service_interval_le_cost.
        apply leq_trans with (n := service rate sched j (job_arrival j + R)); last first.
        {
          unfold valid_sporadic_taskset, is_valid_sporadic_task in *.
          apply service_monotonic; rewrite leq_add2l.
          specialize (JOBPARAMS j); des; rewrite JOBPARAMS1.
          by rewrite JOBtsk.
        }
        rewrite leq_eqVlt; apply/orP; left; rewrite eq_sym.
        by apply COMPLETED.
      Qed.

      (* ..., and the schedulability test yields safe response-time
         bounds for each task. *)
      Theorem edf_schedulability_test_yields_response_time_bounds :
        forall tsk,
          tsk \in ts ->
          exists R,
            R <= task_deadline tsk /\
            forall (j: JobIn arr_seq),
              job_task j = tsk ->
              completed job_cost rate sched j (job_arrival j + R).
      Proof.
        intros tsk IN.
        unfold edf_schedulable in *.
        have BOUNDS := (R_list_has_response_time_bounds).
        have DL := (R_list_le_deadline).
        have HAS := (R_list_has_R_for_every_tsk).
        destruct (R_list_edf ts) as [rt_bounds |]; last by ins.
        exploit (HAS rt_bounds tsk); [by ins | by ins | clear HAS; intro HAS; des].        
        exists R; split.
          by apply DL with (rt_bounds0 := rt_bounds).
          by ins; apply (BOUNDS rt_bounds tsk).
      Qed.

      (* For completeness, since all jobs of the arrival sequence
         are spawned by the task set, we conclude that no job misses
         its deadline. *)
      Theorem jobs_schedulable_by_fp_rta :
        forall (j: JobIn arr_seq), no_deadline_missed_by_job j.
      Proof.
        intros j.
        have SCHED := taskset_schedulable_by_fp_rta.
        unfold no_deadline_missed_by_task, task_misses_no_deadline in *.
        apply SCHED with (tsk := job_task j); last by rewrite eq_refl.
        by apply H_all_jobs_from_taskset.
      Qed.
      
    End Proof.

  End Analysis.

End ResponseTimeIterationEDF.