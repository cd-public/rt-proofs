Require Import Vbase schedule bertogna_edf_theory util_divround util_lemmas
        ssreflect ssrbool eqtype ssrnat seq fintype bigop div path
        workload_fp.

Module ResponseTimeIterationEDF.

  Import Schedule ResponseTimeAnalysisEDF WorkloadBoundFP.

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

        Lemma unzip1_update_bound :
          forall l rt_bounds,
            unzip1 (map (update_bound rt_bounds) l) = unzip1 l.
        Proof.
          induction l; first by done.
          intros rt_bounds.
          simpl; f_equal; last by done.
          by unfold update_bound; desf.
        Qed.

      Lemma unzip1_edf_iteration :
          forall l k,
            unzip1 (iter k edf_rta_iteration (initial_state l)) = l.
        Proof.
          intros l k; clear -k.
          induction k; simpl.
          {
            unfold initial_state.
            induction l; first by done.
            by simpl; rewrite IHl.
          }
          {
            unfold edf_rta_iteration. 
            by rewrite unzip1_update_bound.
          }
        Qed.

        Lemma size_edf_iteration :
          forall l k,
            size (iter k edf_rta_iteration (initial_state l)) = size l.
        Proof.
          intros l k; clear -k.
          induction k; simpl; first by rewrite size_map.
          by rewrite size_map.
        Qed.
        
        Lemma interference_bound_edf_monotonic :
          forall tsk x1 x2 tsk_other R R',
            x1 <= x2 ->
            R <= R' ->
            task_period tsk_other > 0 ->
            task_cost tsk_other <= R ->
            interference_bound_edf task_cost task_period task_deadline tsk x1 (tsk_other, R) <=
            interference_bound_edf task_cost task_period task_deadline tsk x2 (tsk_other, R').
        Proof.
          intros tsk x1 x2 tsk_other R R' LEx LEr GEperiod LEcost.
          unfold interference_bound_edf, interference_bound.
          rewrite leq_min; apply/andP; split.
          {
            rewrite leq_min; apply/andP; split.
            apply leq_trans with (n :=  (minn (W task_cost task_period (fst (tsk_other, R))
                                                                       (snd (tsk_other, R)) x1)
                                              (x1 - task_cost tsk + 1)));
              first by apply geq_minl.
            {
              apply leq_trans with (n := W task_cost task_period (fst (tsk_other, R)) (snd (tsk_other, R)) x1);
                [by apply geq_minl | simpl].
              by apply W_monotonic.
            }
            {
              apply leq_trans with (n := minn (W task_cost task_period (fst (tsk_other, R)) (snd (tsk_other, R)) x1) (x1 - task_cost tsk + 1));
                first by apply geq_minl.
              apply leq_trans with (n := x1 - task_cost tsk + 1);
                first by apply geq_minr.
              by rewrite leq_add2r leq_sub2r.
            }
          }
          {
            apply leq_trans with (n := edf_specific_bound task_cost task_period task_deadline tsk (tsk_other, R));
              first by apply geq_minr.
            unfold edf_specific_bound; simpl.
            rewrite leq_add2l leq_min; apply/andP; split; first by apply geq_minl.
            apply leq_trans with (n := task_deadline tsk %% task_period tsk_other -
                                       (task_deadline tsk_other - R));
              [by apply geq_minr | by rewrite 2?leq_sub2l].
          }
        Qed.


        (* The following lemma states that the response-time bounds
           computed using R_list are valid. *)
        Lemma R_list_ge_cost :
          forall ts rt_bounds tsk R,
            R_list_edf ts = Some rt_bounds ->
            (tsk, R) \in rt_bounds ->
            R >= task_cost tsk.
        Proof.
          intros ts rt_bounds tsk R SOME PAIR.
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
          forall ts rt_bounds tsk R,
            R_list_edf ts = Some rt_bounds ->
            (tsk, R) \in rt_bounds ->
            R <= task_deadline tsk.
        Proof.
          intros ts rt_bounds tsk R SOME PAIR; unfold R_list_edf in SOME.
          destruct (all R_le_deadline (iter (max_steps ts)
                                            edf_rta_iteration (initial_state ts))) eqn:DEADLINE;
            last by done.
          move: DEADLINE => /allP DEADLINE.
          inversion SOME as [EQ]; rewrite -EQ in PAIR.
          by specialize (DEADLINE (tsk, R) PAIR).
        Qed.

        Lemma R_list_has_R_for_every_tsk :
          forall ts rt_bounds tsk,
            R_list_edf ts = Some rt_bounds ->
            tsk \in ts ->
            exists R,
              (tsk, R) \in rt_bounds.
        Proof.
          intros ts rt_bounds tsk SOME IN.
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

      (* In order not to overcount job interference, we assume that
       jobs of the same task do not execute in parallel.
       Our proof requires a definition of interference based on
       the sum of the individual contributions of each job:
         I_total = I_j1 + I_j2 + ...
       Note that under EDF, this is equivalent to task precedence
       constraints. *)
      Hypothesis H_no_intra_task_parallelism:
        jobs_of_same_task_dont_execute_in_parallel job_task sched.

      (* Assume that the schedule satisfies the global scheduling
         invariant with EDF priority, i.e., if any job of tsk is
         backlogged, every processor must be busy with jobs with
         no greater absolute deadline. *)
      Let higher_eq_priority :=
        @EDF Job arr_seq job_deadline. (* TODO: implicit params seems broken *)    
      Hypothesis H_global_scheduling_invariant:
        JLFP_JLDP_scheduling_invariant_holds job_cost num_cpus rate sched higher_eq_priority.

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
            (unzip1 v1 == unzip1 v2) &&
            all (fun p => (snd (fst p)) <= (snd (snd p))) (zip v1 v2).

          set one_lt := fun (v1 v2: list task_with_response_time) =>
            (unzip1 v1 == unzip1 v2) &&
            has (fun p => (snd (fst p)) < (snd (snd p))) (zip v1 v2).

          assert (REFL: reflexive all_le).
          {
            intros l; unfold all_le; rewrite eq_refl andTb.
            destruct l; first by done.
            apply/(zipP (fun x y => snd x <= snd y)); try (by ins).
            by ins; apply leqnn.
          }

          assert (TRANS: transitive all_le).
          {
            unfold transitive, all_le.
            move => y x z /andP [/eqP ZIPxy LExy] /andP [/eqP ZIPyz LEyz].
            apply/andP; split; first by rewrite ZIPxy -ZIPyz.
            move: LExy => /(zipP (fun x y => snd x <= snd y)) LExy.
            move: LEyz => /(zipP (fun x y => snd x <= snd y)) LEyz.
            assert (SIZExy: size (unzip1 x) = size (unzip1 y)).
              by rewrite ZIPxy.
            assert (SIZEyz: size (unzip1 y) = size (unzip1 z)).
              by rewrite ZIPyz.
            rewrite 2!size_map in SIZExy; rewrite 2!size_map in SIZEyz.
            destruct y.
            {
              apply size0nil in SIZExy; symmetry in SIZEyz.
              by apply size0nil in SIZEyz; subst.
            }
            apply/(zipP (fun x y => snd x <= snd y));
              [by apply (t, 0) | by rewrite SIZExy -SIZEyz|]. 
            intros i LTi.
            exploit LExy; first by rewrite SIZExy.
            {
              rewrite size_zip -SIZEyz -SIZExy minnn in LTi.
              by rewrite size_zip -SIZExy minnn; apply LTi.
            }
            instantiate (1 := t); intro LE.
            exploit LEyz; first by apply SIZEyz.
            {
              rewrite size_zip SIZExy SIZEyz minnn in LTi.
              by rewrite size_zip SIZEyz minnn; apply LTi.
            }
            by instantiate (1 := t); intro LE'; apply (leq_trans LE).
          }

          assert (MONiter:forall x1 x2,
                     all_le (initial_state ts) x1 ->
                     all_le x1 x2 ->
                     all_le (edf_rta_iteration x1) (edf_rta_iteration x2)).
          {
            intros x1 x2 LEinit LE.
            move: LE => /andP [/eqP ZIP LE]; unfold all_le.

            assert (UNZIP': unzip1 (edf_rta_iteration x1) = unzip1 (edf_rta_iteration x2)).
            {
              by rewrite 2!unzip1_update_bound.
            }
            
            apply/andP; split; first by rewrite UNZIP'.
            apply f_equal with (B := nat) (f := fun x => size x) in UNZIP'.
            rename UNZIP' into SIZE.
            rewrite size_map [size (unzip1 _)]size_map in SIZE.
            move: LE => /(zipP (fun x y => snd x <= snd y)) LE.
            destruct x1 as [| p0 x1'], x2 as [| p0' x2']; try (by ins).
            apply/(zipP (fun x y => snd x <= snd y));
              [by apply (p0,0) | by done |].

            intros i LTi.
            exploit LE; first by rewrite 2!size_map in SIZE.
            {
              by rewrite size_zip 2!size_map -size_zip in LTi; apply LTi.
            }
            rewrite 2!size_map in SIZE.
            instantiate (1 := p0); intro LEi.
            rewrite (nth_map p0);
              last by rewrite size_zip 2!size_map -SIZE minnn in LTi.
            rewrite (nth_map p0);
              last by rewrite size_zip 2!size_map SIZE minnn in LTi.
            unfold update_bound, response_time_bound; desf; simpl.
            rename s into tsk_i, s0 into tsk_i', n into R_i, n0 into R_i', Heq0 into EQ,Heq1 into EQ'.
            assert (EQtsk: tsk_i = tsk_i').
            {
              destruct p0 as [tsk0 R0], p0' as [tsk0' R0']; simpl in H2; subst.
              have MAP := @nth_map _ (tsk0',R0) _ tsk0' (fun x => fst x) i ((tsk0', R0) :: x1').
              have MAP' := @nth_map _ (tsk0',R0) _ tsk0' (fun x => fst x) i ((tsk0', R0') :: x2').
              assert (FSTeq: fst (nth (tsk0', R0)((tsk0', R0) :: x1') i) = fst (nth (tsk0',R0) ((tsk0', R0') :: x2') i)).
              {
                rewrite -MAP;
                  last by simpl; rewrite size_zip 2!size_map /= -H0 minnn in LTi.
                rewrite -MAP';
                  last by simpl; rewrite size_zip 2!size_map /= H0 minnn in LTi.
                by f_equal; simpl; f_equal.
              }
              apply f_equal with (B := sporadic_task) (f := fun x => fst x) in EQ.
              apply f_equal with (B := sporadic_task) (f := fun x => fst x) in EQ'.
              by rewrite FSTeq EQ' /= in EQ; rewrite EQ.
            }
            subst tsk_i'; rewrite leq_add2l.
            unfold I, total_interference_bound_edf; apply leq_div2r.
            rewrite 2!big_cons.
            destruct p0 as [tsk0 R0], p0' as [tsk0' R0'].
            simpl in H2; subst tsk0'.
            rename R_i into delta, R_i' into delta'.
            rewrite EQ EQ' in LEi; simpl in LEi.
            rename H0 into SIZE, H1 into UNZIP; clear EQ EQ'.

            assert (SUBST: forall l delta,
                      \sum_(j <- l | let '(tsk_other, _) := j in
                        is_interfering_task_jlfp tsk_i tsk_other)
                          (let '(tsk_other, R_other) := j in
                            interference_bound_edf task_cost task_period task_deadline tsk_i delta
                              (tsk_other, R_other)) =
                      \sum_(j <- l | is_interfering_task_jlfp tsk_i (fst j))
                        interference_bound_edf task_cost task_period task_deadline tsk_i delta j).
            {
              intros l x; clear -l.
              induction l; first by rewrite 2!big_nil.
              by rewrite 2!big_cons; rewrite IHl; desf; rewrite /= Heq in Heq0.
            } rewrite 2!SUBST; clear SUBST.
            
            assert (VALID': valid_sporadic_taskset task_cost task_period task_deadline (unzip1 ((tsk0, R0) :: x1'))).
            {
              move: LEinit => /andP [/eqP EQinit _].
              rewrite -EQinit; unfold valid_sporadic_taskset.
              move => tsk /mapP IN. destruct IN as [p INinit EQ]; subst.
              by move: INinit => /mapP INinit; destruct INinit as [tsk INtsk]; subst; apply VALID.
            }

            assert (GE_COST: all (fun p => task_cost (fst p) <= snd p) ((tsk0, R0) :: x1')). 
            {
              clear LE; move: LEinit => /andP [/eqP UNZIP' LE].
              move: LE => /(zipP (fun x y => snd x <= snd y)) LE.
              specialize (LE (tsk0, R0)).
              apply/(all_nthP (tsk0,R0)).
              intros j LTj; generalize UNZIP'; simpl; intro SIZE'.
              have F := @f_equal _ _ size (unzip1 (initial_state ts)).
              apply F in SIZE'; clear F; rewrite /= 3!size_map in SIZE'.
              exploit LE; [by rewrite size_map /= | |].
              {
                rewrite size_zip size_map /= SIZE' minnn.
                by simpl in LTj; apply LTj.
              }
              clear LE; intro LE.
              unfold initial_state in LE.
              have MAP := @nth_map _ tsk0 _ (tsk0,R0).
              rewrite MAP /= in LE;
                [clear MAP | by rewrite SIZE'; simpl in LTj].
              apply leq_trans with (n := task_cost (nth tsk0 ts j));
                [apply eq_leq; f_equal | by done].
              have MAP := @nth_map _ (tsk0, R0) _ tsk0 (fun x => fst x).
              rewrite -MAP; [clear MAP | by done].
              unfold unzip1 in UNZIP'; rewrite -UNZIP'; f_equal.
              clear -ts; induction ts; [by done | by simpl; f_equal].
            }
            move: GE_COST => /allP GE_COST.
            
            assert (LESUM: \sum_(j <- x1' | is_interfering_task_jlfp tsk_i (fst j))
                          interference_bound_edf task_cost task_period task_deadline tsk_i delta j <=                                  \sum_(j <- x2' | is_interfering_task_jlfp tsk_i (fst j))
                          interference_bound_edf task_cost task_period task_deadline tsk_i delta' j).
            {
              set elem := (tsk0, R0); rewrite 2!(big_nth elem).
              rewrite -SIZE.
              rewrite big_mkcond [\sum_(_ <- _ | is_interfering_task_jlfp _ _)_]big_mkcond.
              rewrite big_seq_cond [\sum_(_ <- _ | true) _]big_seq_cond.
              apply leq_sum; intros j; rewrite andbT; intros INj.
              rewrite mem_iota add0n subn0 in INj; move: INj => /andP [_ INj].
              assert (FSTeq: fst (nth elem x1' j) = fst (nth elem x2' j)).
              {
                have MAP := @nth_map _ elem _ tsk0 (fun x => fst x).
                by rewrite -2?MAP -?SIZE //; f_equal.
              } rewrite -FSTeq.
              destruct (is_interfering_task_jlfp tsk_i (fst (nth elem x1' j))) eqn:INTERF;
                last by done.
              {
                exploit (LE elem); [by rewrite /= SIZE | | intro LEj].
                {
                  rewrite size_zip 2!size_map /= -SIZE minnn in LTi.
                  by rewrite size_zip /= -SIZE minnn; apply (leq_ltn_trans INj).
                }
                simpl in LEj.
                exploit (VALID' (fst (nth elem x1' j))); last intro VALIDj.
                {
                  apply/mapP; exists (nth elem x1' j); last by done.
                  by rewrite in_cons; apply/orP; right; rewrite mem_nth.
                }
                exploit (GE_COST (nth elem x1' j)); last intro GE_COSTj.
                {
                  by rewrite in_cons; apply/orP; right; rewrite mem_nth.
                }
                unfold is_valid_sporadic_task in *.
                destruct (nth elem x1' j) as [tsk_j R_j], (nth elem x2' j) as [tsk_j' R_j'].
                simpl in FSTeq; rewrite -FSTeq; simpl in LEj; simpl in VALIDj; des.
                by apply interference_bound_edf_monotonic.
              }
            }
            destruct (is_interfering_task_jlfp tsk_i tsk0) eqn:INTERFtsk0; last by done.
            apply leq_add; last by done.
            {             
              exploit (LE (tsk0, R0)); [by rewrite /= SIZE | | intro LEj];
                first by instantiate (1 := 0); rewrite size_zip /= -SIZE minnn.
              exploit (VALID' tsk0); first by rewrite in_cons; apply/orP; left.
              exploit (GE_COST (tsk0, R0)); first by rewrite in_cons eq_refl orTb.
              unfold is_valid_sporadic_task; intros GE_COST0 VALID0; des; simpl in LEj.
              by apply interference_bound_edf_monotonic.
            }
          }

          assert (INIT': forall step, all_le (initial_state ts) (iter step edf_rta_iteration (initial_state ts))).
          {
            intros step; destruct step; first by apply REFL.
            apply/andP; split.
            {
              assert (UNZIP0 := unzip1_edf_iteration ts 0).
              by simpl in UNZIP0; rewrite UNZIP0 unzip1_edf_iteration.
            }  
            destruct ts as [| tsk0 ts'].
            {
              clear -step; induction step; first by done.
              by rewrite iterSr IHstep.
            }

            apply/(zipP (fun x y => snd x <= snd y));
              [by apply (tsk0,0)|by rewrite size_edf_iteration size_map |].
            
            intros i LTi; rewrite iterS; unfold edf_rta_iteration at 1.
            have MAP := @nth_map _ (tsk0,0) _ (tsk0,0).
            rewrite size_zip size_edf_iteration size_map minnn in LTi.
            rewrite MAP; clear MAP; last by rewrite size_edf_iteration.
            destruct (nth (tsk0, 0) (initial_state (tsk0 :: ts')) i) as [tsk_i R_i] eqn:SUBST.
            rewrite SUBST; unfold update_bound.
            unfold initial_state in SUBST.
            have MAP := @nth_map _ tsk0 _ (tsk0, 0).
            rewrite ?MAP // in SUBST; inversion SUBST; clear MAP. 
            assert (EQtsk: tsk_i = fst (nth (tsk0, 0) (iter step edf_rta_iteration (initial_state (tsk0 :: ts'))) i)).
            {
              have MAP := @nth_map _ (tsk0,0) _ tsk0 (fun x => fst x).
              rewrite -MAP; clear MAP; last by rewrite size_edf_iteration.
              have UNZIP := unzip1_edf_iteration; unfold unzip1 in UNZIP.
              by rewrite UNZIP; symmetry. 
            }
            destruct (nth (tsk0, 0) (iter step edf_rta_iteration (initial_state (tsk0 :: ts')))) as [tsk_i' R_i'].
            by simpl in EQtsk; rewrite -EQtsk; subst; apply leq_addr.
          }
          
          assert (GROWS: forall k, all_le (f k) (f k.+1)).
          {
            unfold f; intros k.
            apply fun_mon_iter_mon_generic with (x1 := k) (x2 := k.+1);
              try (by ins); first by apply leqnSn.
          } clear MONiter INIT' REFL TRANS.
          
          (* Either f converges by the deadline or not. *)
          unfold max_steps in *.
          set sum_d := \sum_(tsk <- ts) task_deadline tsk.
          destruct ([exists k in 'I_(sum_d.+1), f k == f k.+1]) eqn:EX.
          {
            move: EX => /exists_inP EX; destruct EX as [k _ ITERk].
            move: ITERk => /eqP ITERk.
            apply iter_fix with (k := k);
              [by ins | by rewrite -ltnS; apply ltn_ord].
          }
          
          apply negbT in EX; rewrite negb_exists_in in EX.
          move: EX => /forall_inP EX.

          assert (GT: forall k: 'I_(sum_d.+1), one_lt (f k) (f k.+1)).
          {
            intros step; unfold one_lt; apply/andP; split;
              first by rewrite 2!unzip1_edf_iteration.
            rewrite -[has _ _]negbK; apply/negP; unfold not; intro ALL.
            rewrite -all_predC in ALL.
            move: ALL => /allP ALL.
            exploit (EX step); [by done | intro DIFF].
            assert (DUMMY: exists tsk: sporadic_task, True).
            {
              unfold f, edf_rta_iteration, initial_state in DIFF.
              destruct ts as [| tsk0 ts']; last by exists tsk0.
              assert (EMPTY: forall k,
                        iter k (fun x => [seq update_bound x i | i <- x]) [::] = [::]).
              {
                induction k; [by done | by rewrite iterS IHk].
              }
              by rewrite 2!EMPTY in DIFF.
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
              move: GROWS => /andP [_ /allP GROWS].
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

          unfold f; destruct ts as [| tsk0 ts'].
          {
            clear -Heq.
            induction sum_d; first by unfold edf_rta_iteration. 
            by rewrite [iter sum_d.+2 _ _]iterS -IHsum_d -iterS.
          }
          
          assert (EXCEEDS: forall step: 'I_(sum_d.+1),
                             \sum_(p <- f step) snd p > step).
          {
            intro step; destruct step as [step LT].
            induction step.
            {
              simpl.
              apply leq_ltn_trans with (n :=
                 \sum_(p <- (tsk0, task_cost tsk0) :: initial_state ts') 0);
                first by rewrite big_const_seq iter_addn mul0n addn0.
              apply leq_trans with (n :=
                 \sum_(p <- (tsk0, task_cost tsk0) :: initial_state ts') 1);
                first by rewrite 2!big_const_seq 2!iter_addn mul0n mul1n 2!addn0.
              rewrite big_seq_cond [\sum_(p <- _ | true) _]big_seq_cond.
              apply leq_sum.
              intro p; rewrite andbT; simpl; intros IN.
              destruct p as [tsk R]; simpl in *.
              rewrite in_cons in IN; move: IN => /orP [/eqP HEAD | TAIL].
              {
                inversion HEAD; subst.
                exploit (VALID tsk0);
                  first by rewrite in_cons; apply/orP; left.
                unfold valid_sporadic_taskset, is_valid_sporadic_task.
                by unfold task_deadline_positive; ins; des.
              }
              {
                move: TAIL => /mapP TAIL; destruct TAIL as [x IN SUBST].
                inversion SUBST; subst; clear SUBST.
                exploit (VALID x);
                  first by rewrite in_cons; apply/orP; right.
                unfold valid_sporadic_taskset, is_valid_sporadic_task.
                by unfold task_deadline_positive; ins; des.
              }
            }
            {
              assert (LT': step < sum_d.+1).
                by apply leq_ltn_trans with (n := step.+1).
              simpl in *; exploit IHstep; [by done | intro LE].
              specialize (GT (Ordinal LT')).
              simpl in *; clear LT LT' IHstep.
              move: GT => /andP [_ /hasP GT]; destruct GT as [p IN LTpair].
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
              move: GROWS => /andP [_ /(zipP (fun x y => snd x <= snd y)) GROWS].
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
          assert (LT: sum_d < sum_d.+1); first by apply ltnSn.
          specialize (EXCEEDS (Ordinal LT)); simpl in EXCEEDS.
          fold sum_d in Heq; move: Heq => ALL; clear -EXCEEDS ALL.

          assert (SUM: \sum_(p <- f sum_d) snd p <= sum_d).
          {
            unfold sum_d at 2.
            move: ALL => /allP ALL.
            unfold f.
            apply leq_trans with (n := \sum_(p <- iter
                        sum_d edf_rta_iteration (initial_state (tsk0 :: ts'))) task_deadline (fst p)).
            {
              rewrite big_seq_cond [\sum_(_ <- _ | true) _]big_seq_cond.
              apply leq_sum; intro p; rewrite andbT; intro IN.
              by specialize (ALL p IN); destruct p.
            }
            have MAP := @big_map _ 0 addn _ _ (fun x => fst x) (f sum_d)
                                 (fun x => true) (fun x => task_deadline x).
            rewrite -MAP; clear MAP.
            apply eq_leq, congr_big; [| by done | by done].
            by rewrite -(unzip1_edf_iteration (tsk0 :: ts') sum_d).
          }
          by rewrite ltnNge SUM in EXCEEDS.
        Qed.
        
        Lemma R_list_converges :
          forall tsk R rt_bounds,
            R_list_edf ts = Some rt_bounds ->
            (tsk, R) \in rt_bounds ->
            R = task_cost tsk + div_floor (I rt_bounds tsk R) num_cpus.
        Proof.
          intros tsk R rt_bounds SOME IN.
          have CONV := R_list_converges_helper rt_bounds.
          unfold R_list_edf in *; desf.
          exploit (CONV); [by done | by done | intro ITER; clear CONV].

          cut (update_bound (iter (max_steps ts)
                 edf_rta_iteration (initial_state ts)) (tsk,R) = (tsk, R)).
          {
            intros EQ.
            have F := @f_equal _ _ (fun x => snd x) _ (tsk, R).
            by apply F in EQ; simpl in EQ.
          }
          set s := iter (max_steps ts) edf_rta_iteration (initial_state ts).
          fold s in ITER, IN.
          move: IN => /(nthP (tsk,0)) IN; destruct IN as [i LT EQ].
          generalize EQ; rewrite ITER iterS in EQ; intro EQ'.
          fold s in EQ.
          unfold edf_rta_iteration in EQ.
          have MAP := @nth_map _ (tsk,0) _ _ (update_bound s). 
          by rewrite MAP // EQ' in EQ; rewrite EQ.
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
          unfold is_response_time_bound_of_task in *.
          apply BOUND with (task_cost := task_cost) (task_period := task_period)
             (task_deadline := task_deadline) (job_deadline := job_deadline)
             (job_task := job_task) (ts := ts) (tsk := tsk) (rt_bounds := rt_bounds); try (by ins).
            by unfold R_list_edf in SOME; desf; rewrite unzip1_edf_iteration.
            by ins; apply R_list_converges.
            by ins; rewrite (R_list_le_deadline ts rt_bounds).
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
        have DL := (R_list_le_deadline ts).
        have HAS := (R_list_has_R_for_every_tsk ts).
        
        destruct (R_list_edf ts) as [rt_bounds |]; last by ins.
        exploit (HAS rt_bounds tsk); [by ins | by ins | clear HAS; intro HAS; des].
        exploit (RLIST rt_bounds tsk R);
          [by ins | by ins | by apply JOBtsk | intro COMPLETED ].
        exploit (DL rt_bounds tsk R);
          [by ins | by ins | clear DL; intro DL].
   
        rewrite eqn_leq; apply/andP; split; first by apply service_interval_le_cost.
        apply leq_trans with (n := service rate sched j (job_arrival j + R)); last first.
        {
          unfold valid_sporadic_taskset, is_valid_sporadic_task in *.
          apply extend_sum; rewrite // leq_add2l.
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
        have DL := (R_list_le_deadline ts).
        have HAS := (R_list_has_R_for_every_tsk ts).
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