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
          
          assert (MON: forall x1 x2, x1 <= x2 -> all_le (f x1) (f x2)).
          {
            intros x1 x2 LE; apply/allP.
            intros x IN; destruct x as [p_i p_i']; simpl.
            admit.
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

          assert (GROWS: forall k: 'I_(sum_d), all_le (f k) (f k.+1)).
          {
            intros k; unfold one_lt.
            by apply MON, leqnSn.
          }

          (* If it doesn't converge, then it becomes larger than the deadline.
             But initialy we assumed otherwise. Contradiction! *)

          assert (LE_MAX: all (fun x => task_deadline x <= sum_d) ts).
          {
            apply/allP; ins; unfold sum_d.
            by rewrite (big_rem x); [by apply leq_addr | by done].
          } 
          
          unfold f.
          unfold initial_state in *.
          destruct (ts) as [| tsk0 ts'].
          {
            induction sum_d; unfold edf_rta_iteration; first by done.
            rewrite iterS [iter sum_d.+2 _ _]iterS.
            rewrite -IHsum_d ?IHsum_d; try (by done);
            intros x; assert (LT: x < sum_d.+1);
            try (ins; apply (EX (Ordinal LT)));
            try (ins; apply (GROWS (Ordinal LT)));
            by apply leq_trans with (n := sum_d).
          }          

          (*assert (DLZERO: sum_d <= 0 ->
                          forall tsk, tsk \in ts -> task_deadline tsk = 0).
          {
            rewrite leqn0; unfold sum_d; intro ZERO.
            rewrite -sum_nat_eq0_nat in ZERO.
            move: ZERO => /allP ZERO.
            by ins; apply/eqP; apply ZERO.
          }
          unfold sum_d in DLZERO.*)

          assert (BY1: has (fun x => ~~ (R_le_deadline x)) (f sum_d)).
          {
            clear MON EX.
            remember sum_d as SUM_D.
            unfold sum_d in *; clear sum_d; rename HeqSUM_D into LE.
            move: LE => /eqP LE; rewrite eqn_leq in LE.
            move: LE => /andP [LE _].
            induction SUM_D.
            {
              move: LE_MAX => /andP [LE_MAX _].
              rewrite leqn0 in LE_MAX; move: LE_MAX => /eqP LE_MAX.
              simpl; rewrite -ltnNge LE_MAX; apply/orP; left.
              exploit (VALID tsk0); first by rewrite in_cons eq_refl orTb.
              unfold valid_sporadic_taskset, is_valid_sporadic_task.
              by ins; des.
            }
            {
              exploit IHSUM_D; try (by apply ltnW).
              {
                intros k; assert (LT: k < SUM_D.+1).
                  by apply leq_trans with (n := SUM_D).
                by apply (GROWS (Ordinal LT)).
              }
              {
              }
              {
                move => /hasP HAS; destruct HAS as [p IN LT].
                assert (LT': SUM_D < SUM_D.+1). by apply ltnSn.
                specialize (GROWS (Ordinal LT')); simpl in GROWS.
                unfold f at 2 in GROWS.
                rewrite -iterS in GROWS.
                fold (f SUM_D.+1) in GROWS.
                move: GROWS => /allP GROWS.
                generalize IN; intro IN'.
                apply (nth_index (tsk0, 0)) in IN'.
                set p_i := nth (tsk0,0) (f SUM_D) (index p (f SUM_D)).
                set p_i' := nth (tsk0,0) (f SUM_D.+1) (index p (f SUM_D)).
                assert (IN'': p_i' \in f SUM_D.+1).
                {
                  admit.
                }
                assert (SAMETSK: fst p_i = fst p_i').
                {
                  admit.
                }
                exploit (GROWS (p_i, p_i')).
                {
                  admit.
                }
                {
                  intro LT_R; simpl in LT_R.
                  apply/hasP; exists p_i'; first by done.
                  unfold R_le_deadline in *; desf; rewrite -ltnNge.
                  apply leq_trans with (n := snd p_i); last by done.
                  unfold p_i in *; rewrite IN' ltnNge.
                  by simpl in SAMETSK; rewrite -SAMETSK IN' /=.
                }
              }
            }
          }
          move: BY1 => /hasP BY1; destruct BY1 as [p IN GT].
          move: Heq => /allP DL.
          exploit (DL p); last by intro BUG; rewrite BUG in GT.
          {
            admit.
          }
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