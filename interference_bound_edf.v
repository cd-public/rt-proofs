Require Import Vbase task job task_arrival schedule platform interference
        workload workload_bound schedulability priority response_time
        bertogna_fp_theory util_divround util_lemmas
        ssreflect ssrbool eqtype ssrnat seq fintype bigop div path.

  (* In the following section, we define Bertogna and Cirinei's
     EDF-specific per-task interference bound. *)
Module EDFSpecificBound.

  Import Job SporadicTaskset ScheduleOfSporadicTask Workload Schedulability ResponseTime
         Priority SporadicTaskArrival Interference.

  Section EDFBoundDef.
    
    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> nat.
    Variable task_period: sporadic_task -> nat.
    Variable task_deadline: sporadic_task -> nat.
    
    (* Let tsk be the task to be analyzed. *)
    Variable tsk: sporadic_task.

    (* Consider the interference incurred by tsk in a window of length delta... *)
    Variable delta: time.

    (* due to a different task tsk_other, with response-time bound R_other. *)
    Variable tsk_other: sporadic_task.
    Variable R_other: time.

    (* Bertogna and Cirinei define the following bound for task interference
       under EDF scheduling. *)
    Definition edf_specific_interference_bound :=
      let d_tsk := task_deadline tsk in
      let e_other := task_cost tsk_other in
      let p_other := task_period tsk_other in
      let d_other := task_deadline tsk_other in
        (div_floor d_tsk p_other) * e_other +
        minn e_other ((d_tsk %% p_other) - (d_other - R_other)).

  End EDFBoundDef.

  Section ProofInterferenceBound.

    Import Schedule Interference Platform SporadicTaskset.
    
    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> nat.
    Variable task_period: sporadic_task -> nat.
    Variable task_deadline: sporadic_task -> nat.
    
    Context {Job: eqType}.
    Variable job_cost: Job -> nat.
    Variable job_deadline: Job -> nat.
    Variable job_task: Job -> sporadic_task.
    
    (* Assume any job arrival sequence... *)
    Context {arr_seq: arrival_sequence Job}.

    (* ... in which jobs arrive sporadically and have valid parameters. *)
    Hypothesis H_sporadic_tasks:
      sporadic_task_model task_period arr_seq job_task.
    Hypothesis H_valid_job_parameters:
      forall (j: JobIn arr_seq),
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j.

    (* Consider any schedule such that...*)
    Variable num_cpus: nat.
    Variable rate: Job -> processor num_cpus -> nat.
    Variable sched: schedule num_cpus arr_seq.

    (* ...jobs do not execute before their arrival times nor longer
       than their execution costs. *)
    Hypothesis H_jobs_must_arrive_to_execute:
      jobs_must_arrive_to_execute sched.
    Hypothesis H_completed_jobs_dont_execute:
      completed_jobs_dont_execute job_cost rate sched.

    (* Also assume that jobs do not execute in parallel, processors have
       unit speed, and that there exists at least one processor. *)
    Hypothesis H_no_parallelism:
      jobs_dont_execute_in_parallel sched.
    Hypothesis H_rate_equals_one :
      forall j cpu, rate j cpu = 1.
    Hypothesis H_at_least_one_cpu :
      num_cpus > 0.

    (* In order not to overcount job interference, we assume that
       jobs of the same task do not execute in parallel.
       Note that under EDF, this is equivalent to task precedence
       constraints.
       This is required because our proof uses a definition of
       interference based on the sum of the individual contributions
       of each job: I_total = I_j1 + I_j2 + ... *)
    Hypothesis H_no_intra_task_parallelism:
      jobs_of_same_task_dont_execute_in_parallel job_task sched.

    (* Assume that we have a task set where all tasks have valid
       parameters and restricted deadlines. *)
    Variable ts: taskset_of sporadic_task.
    Hypothesis all_jobs_from_taskset:
      forall (j: JobIn arr_seq), job_task j \in ts.
    Hypothesis H_valid_task_parameters:
      valid_sporadic_taskset task_cost task_period task_deadline ts.
    Hypothesis H_restricted_deadlines:
      forall tsk, tsk \in ts -> task_deadline tsk <= task_period tsk.

    Let no_deadline_is_missed_by_tsk (tsk: sporadic_task) :=
      task_misses_no_deadline job_cost job_deadline job_task rate sched tsk.
    Let response_time_bounded_by (tsk: sporadic_task) :=
      is_response_time_bound_of_task job_cost job_task tsk rate sched.

    (* Assume that the schedule satisfies the global scheduling invariant
       for EDF, i.e., if any job of tsk is backlogged, every processor
       must be busy with jobs with no larger absolute deadline. *)
    Let higher_eq_priority := @EDF Job arr_seq job_deadline. (* TODO: implicit params broken *)    
    Hypothesis H_global_scheduling_invariant:
      JLFP_JLDP_scheduling_invariant_holds job_cost num_cpus rate sched higher_eq_priority.

    (* Let tsk_i be the task to be analyzed, ...*)
    Variable tsk_i: sporadic_task.
    Hypothesis H_tsk_i_in_task_set: tsk_i \in ts.
    
    (* and j_i one of its jobs. *)
    Variable j_i: JobIn arr_seq.
    Hypothesis H_job_of_tsk_i: job_task j_i = tsk_i.

    (* Let tsk_k denote any interfering task, ... *)
    Variable tsk_k: sporadic_task.
    Hypothesis H_tsk_k_in_task_set: tsk_k \in ts.

    (* ...and R_k its response-time bound. *)
    Variable R_k: time.
    Hypothesis H_R_k_le_deadline: R_k <= task_deadline tsk_k.
    
    (* Consider a time window of length delta <= D_i, starting with j_i's arrival time. *)
    Variable delta: time.
    Hypothesis H_delta_le_deadline: delta <= task_deadline tsk_i.

    (* Assume that the jobs of tsk_k satisfy the response-time bound before the end of the interval *)
    Hypothesis H_all_previous_jobs_completed_on_time :
      forall (j_k: JobIn arr_seq),
        job_task j_k = tsk_k ->
        job_arrival j_k + R_k < job_arrival j_i + delta ->
        completed job_cost rate sched j_k (job_arrival j_k + R_k).

    (* In this section, we prove that the workload of a task in the
       interval [t1, t1 + delta) is bounded by W. *)
    Section MainProof.
                                    
      (* Let's call x the task interference incurred by job j due to tsk_k. *)
      Let x :=
        task_interference job_cost job_task rate sched j_i
                          tsk_k (job_arrival j_i) (job_arrival j_i + delta).

      (* Also, recall the EDF-specific interference bound for EDF. *)
      Let interference_bound :=
        edf_specific_interference_bound task_cost task_period task_deadline tsk_i tsk_k R_k.

      (* Let's simplify the names a bit. *)
      Let t1 := job_arrival j_i.
      Let t2 := job_arrival j_i + delta.
      Let D_i := task_deadline tsk_i.
      Let D_k := task_deadline tsk_k.
      Let p_k := task_period tsk_k.

      Let n_k := div_floor D_i p_k.
      
      (* Identify the subset of jobs that actually cause interference *)
      Let interfering_jobs :=
        filter (fun (x: JobIn arr_seq) =>
                 (job_task x == tsk_k) && (job_interference job_cost rate sched j_i x t1 t2 != 0))
               (jobs_scheduled_between sched t1 t2).

      (* Let's give a simpler name to job interference. *)
      Let interference_caused_by := job_interference job_cost rate sched j_i.
      
      (* Now, consider the list of interfering jobs sorted by arrival time. *)
      Let order := fun (x y: JobIn arr_seq) => job_arrival x <= job_arrival y.
      Let sorted_jobs := (sort order interfering_jobs).

      (* Now we proceed with the proof.
         The first step consists in simplifying the sum corresponding to the workload. *)
      Section SimplifyJobSequence.

        (* Use the alternative definition of task interference, based on
           individual job interference. *)
        Lemma interference_bound_edf_use_another_definition :
          x = \sum_(j <- jobs_scheduled_between sched t1 t2 | job_task j == tsk_k)
                interference_caused_by j t1 t2.
        Proof.
          by apply interference_eq_interference_joblist.
        Qed.

        (* Remove the elements that we don't care about from the sum *)
        Lemma interference_bound_edf_simpl_by_filtering_interfering_jobs :
          \sum_(j <- jobs_scheduled_between sched t1 t2 | job_task j == tsk_k)
             interference_caused_by j t1 t2 = 
          \sum_(j <- interfering_jobs) interference_caused_by j t1 t2.
        Proof.
          unfold interfering_jobs; rewrite big_filter.
          rewrite big_mkcond; rewrite [\sum_(_ <- _ | _) _]big_mkcond /=.
          apply eq_bigr; intros i _; clear -i.
          destruct (job_task i == tsk_k); rewrite ?andTb ?andFb; last by done.
          destruct (job_interference job_cost rate sched j_i i t1 t2 != 0) eqn:DIFF; first by done.
          by apply negbT in DIFF; rewrite negbK in DIFF; apply/eqP.
        Qed.

        (* Then, we consider the sum over the sorted sequence of jobs. *)
        Lemma interference_bound_edf_simpl_by_sorting_interfering_jobs :
          \sum_(j <- interfering_jobs) interference_caused_by j t1 t2 =
           \sum_(j <- sorted_jobs) interference_caused_by j t1 t2.
        Proof.
          by rewrite (eq_big_perm sorted_jobs) /=; last by rewrite -(perm_sort order).
        Qed.

        (* Remember that both sequences have the same set of elements.
           TODO: check if really necessary. *)
        Lemma interference_bound_edf_job_in_same_sequence :
          forall j,
            (j \in interfering_jobs) = (j \in sorted_jobs).
        Proof.
          by apply perm_eq_mem; rewrite -(perm_sort order).
        Qed.

        (* Remember that all jobs in the sorted sequence is an interfering job of tsk_k. *)
        Lemma interference_bound_edf_all_jobs_from_tsk_k :
          forall j,
            j \in sorted_jobs ->
            job_task j = tsk_k /\
            interference_caused_by j t1 t2 != 0 /\
            j \in jobs_scheduled_between sched t1 t2.
        Proof.
          intros j LT.
          rewrite -interference_bound_edf_job_in_same_sequence mem_filter in LT.
          by move: LT => /andP [/andP [/eqP JOBi SERVi] INi]; repeat split.
        Qed.

        (* Remember that consecutive jobs are ordered by arrival. *)
        Lemma interference_bound_edf_jobs_ordered_by_arrival :
          forall i elem,
            i < (size sorted_jobs).-1 ->
            order (nth elem sorted_jobs i) (nth elem sorted_jobs i.+1).
        Proof.
          intros i elem LT.
          assert (SORT: sorted order sorted_jobs).
            by apply sort_sorted; unfold total, order; ins; apply leq_total.
          by destruct sorted_jobs; simpl in *; [by rewrite ltn0 in LT | by apply/pathP].
        Qed.

        (* Remember that for any job of tsk_k, service <= task_cost tsk *)
        Lemma interference_bound_edf_interference_le_task_cost :
          forall j (INi: j \in interfering_jobs),
            interference_caused_by j t1 t2 <= task_cost tsk_k.
        Proof.
          rename H_valid_job_parameters into PARAMS,
                 H_rate_equals_one into RATE.
          intros j; rewrite mem_filter; move => /andP [/andP [/eqP JOBj _] _].
          specialize (PARAMS j); des.
          apply leq_trans with (n := service_during rate sched j t1 t2);
            first by apply job_interference_le_service; ins; rewrite RATE.
          by apply cumulative_service_le_task_cost with (job_task0 := job_task)
                              (task_deadline0 := task_deadline) (job_cost0 := job_cost)
                                                        (job_deadline0 := job_deadline).
        Qed.

      End SimplifyJobSequence.

      (* Next, we prove some facts relating job deadlines and interference under EDF.*)
      Section FactsAboutEDF.

        (* Under EDF scheduling, a job only causes interference if its deadline
           is not larger than the deadline of the analyzed job. 
           TODO: Should this be in the interference.v file? *)
        Lemma interference_under_edf_implies_shorter_deadlines :
          forall (j j': JobIn arr_seq) t1 t2,
            job_interference job_cost rate sched j' j t1 t2 != 0 ->
            job_arrival j + job_deadline j <= job_arrival j' + job_deadline j'.
        Proof.
          rename H_global_scheduling_invariant into INV.
          clear - t1 t2 INV; clear t1 t2.
          intros j j' t1 t2 INTERF.
          unfold job_interference in INTERF.
          destruct ([exists t': 'I_t2, (t' >= t1) && backlogged job_cost rate sched j' t' &&
                                                  scheduled sched j t']) eqn:EX.
          {
            move: EX => /existsP EX; destruct EX as [t' EX];move: EX => /andP [/andP [LE BACK] SCHED].
            eapply interfering_job_has_higher_eq_prio in BACK;
              [ | by apply INV | by apply SCHED].
            by apply BACK.
          }
          {
            apply negbT in EX; rewrite negb_exists in EX; move: EX => /forallP ALL. 
            rewrite big_nat_cond (eq_bigr (fun x => 0)) in INTERF;
              first by rewrite -big_nat_cond big_const_nat iter_addn mul0n  addn0 eq_refl in INTERF.
            intros i; rewrite andbT; move => /andP [GT LT].
            specialize (ALL (Ordinal LT)); simpl in ALL.
            rewrite -andbA negb_and -implybE in ALL; move: ALL => /implyP ALL.
            by specialize (ALL GT); apply/eqP; rewrite eqb0.
          }
        Qed.

      End FactsAboutEDF.

      (* Next, we show that if the number of jobs is no larger than n_k,
         the workload bound trivially holds. *)
      Section InterferenceFewJobs.

        Hypothesis H_few_jobs: size sorted_jobs <= n_k.
        
        Lemma interference_bound_edf_holds_for_at_most_n_k_jobs :
           \sum_(j <- sorted_jobs) interference_caused_by j t1 t2 <=
             interference_bound.
        Proof.
          rename H_rate_equals_one into RATE.
          rewrite -[\sum_(_ <- _ | _) _]addn0 leq_add //.
          apply leq_trans with (n := \sum_(x <- sorted_jobs) task_cost tsk_k);
            last by rewrite big_const_seq iter_addn addn0 mulnC leq_mul2r; apply/orP; right.
          {
            rewrite [\sum_(_ <- _) interference_caused_by _ _ _]big_seq_cond.
            rewrite [\sum_(_ <- _) task_cost _]big_seq_cond.
            apply leq_sum; intros i; move/andP => [INi _].
            rewrite -interference_bound_edf_job_in_same_sequence in INi.
            by apply interference_bound_edf_interference_le_task_cost.
          }
        Qed.

      End InterferenceFewJobs.

      (* Otherwise, assume that the number of jobs is larger than n_k >= 0. *)
      Section InterferenceManyJobs.

        Hypothesis H_many_jobs: n_k < size sorted_jobs.

        (* This of course implies that there's at least one job. *)
        Lemma interference_bound_edf_at_least_one_job: size sorted_jobs > 0.
        Proof.
          by apply leq_ltn_trans with (n := n_k).
        Qed.

        (* Let j_fst be the first job, and a_fst its arrival time. *)
        Variable elem: JobIn arr_seq.
        Let j_fst := nth elem sorted_jobs 0.
        Let a_fst := job_arrival j_fst.

        (* In this section, we prove some basic lemmas about j_fst. *)
        Section FactsAboutFirstJob.
          
          (* The first job is an interfering job of task tsk_k. *)
          Lemma interference_bound_edf_j_fst_is_job_of_tsk_k :
            job_task j_fst = tsk_k /\
            interference_caused_by j_fst t1 t2 != 0 /\
            j_fst \in jobs_scheduled_between sched t1 t2.
          Proof.
            by apply interference_bound_edf_all_jobs_from_tsk_k, mem_nth,
                     interference_bound_edf_at_least_one_job.
          Qed.

          (* The deadline of j_fst is the deadline of tsk_k. *)
          Lemma interference_bound_edf_j_fst_deadline :
            job_deadline j_fst = task_deadline tsk_k.
          Proof.
            unfold valid_sporadic_job in *.
            rename H_valid_job_parameters into PARAMS.
            have FST := interference_bound_edf_j_fst_is_job_of_tsk_k.
            destruct FST as [FSTtask _].
            by specialize (PARAMS j_fst); des; rewrite PARAMS1 FSTtask.
          Qed.

          (* The deadline of j_i is the deadline of tsk_i. *)
          Lemma interference_bound_edf_j_i_deadline :
            job_deadline j_i = task_deadline tsk_i.
          Proof.
            unfold valid_sporadic_job in *.
            rename H_valid_job_parameters into PARAMS,
                   H_job_of_tsk_i into JOBtsk.
            by specialize (PARAMS j_i); des; rewrite PARAMS1 JOBtsk.
          Qed.

          (* If j_fst completes by its response-time bound, then t1 <= a_fst + R_k,
             where t1 is the beginning of the time window (arrival of j_i). *)
          Lemma interference_bound_edf_j_fst_completion_implies_rt_bound_inside_interval :
            completed job_cost rate sched j_fst (a_fst + R_k) ->
            t1 <= a_fst + R_k.
          Proof.
            rename H_rate_equals_one into RATE.
            intros RBOUND.
            rewrite leqNgt; apply/negP; unfold not; intro BUG.
            have FST := interference_bound_edf_j_fst_is_job_of_tsk_k.
            destruct FST as [_ [ FSTserv _]].
            move: FSTserv => /negP FSTserv; apply FSTserv.
            rewrite -leqn0; apply leq_trans with (n := service_during rate sched j_fst t1 t2);
              first by apply job_interference_le_service; ins; rewrite RATE.
            rewrite leqn0; apply/eqP.
            by apply cumulative_service_after_job_rt_zero with (job_cost0 := job_cost) (R := R_k);
              try (by done); apply ltnW.
          Qed. 
          
        End FactsAboutFirstJob.
        
        (* Now, let's prove the interference bound for the particular case with a single job.
           This case must be dealt with separately because the single job can be both
           carry-in and carry-out at the same time, so its response time is not necessarily
           bounded by R_k (from the hypothesis H_all_previous_jobs_completed_on_time). *)
        Section InterferenceSingleJob.

          (* Assume that there's at least one job in the sorted list. *)
          Hypothesis H_only_one_job: size sorted_jobs = 1.
          
          (* Since there's only one job, we simplify the terms in the interference bound. *)
          Lemma interference_bound_edf_simpl_when_there's_one_job :
            D_i %% p_k - (D_k - R_k) = D_i - (D_k - R_k).
          Proof.
            rename H_many_jobs into NUM,
                   H_valid_task_parameters into TASK_PARAMS,
                   H_tsk_k_in_task_set into INk.
            unfold valid_sporadic_taskset, is_valid_sporadic_task,
                   interference_bound, edf_specific_interference_bound in *.
            rewrite H_only_one_job in NUM.
            rewrite ltnS leqn0 in NUM; move: NUM => /eqP EQnk.
            move: EQnk => /eqP EQnk; unfold n_k, div_floor in EQnk.
            rewrite -leqn0 leqNgt divn_gt0 in EQnk;
              last by specialize (TASK_PARAMS tsk_k INk); des.
            by rewrite -ltnNge in EQnk; rewrite modn_small //.
          Qed.

          (* Next, we show that if j_fst completes by its response-time bound R_k,
             then then interference bound holds. *)
          Section ResponseTimeOfSingleJobBounded.

            Hypothesis H_j_fst_completed_by_rt_bound :
              completed job_cost rate sched j_fst (a_fst + R_k).
            
            Lemma interference_bound_edf_holds_for_single_job_that_completes_on_time :
              job_interference job_cost rate sched j_i j_fst t1 t2 <= D_i - (D_k - R_k).
            Proof.
              rename H_j_fst_completed_by_rt_bound into RBOUND.
              have AFTERt1 :=
                interference_bound_edf_j_fst_completion_implies_rt_bound_inside_interval RBOUND.
              have FST := interference_bound_edf_j_fst_is_job_of_tsk_k.
              destruct FST as [_ [ LEdl _]].            
              apply interference_under_edf_implies_shorter_deadlines in LEdl.
              destruct (D_k - R_k <= D_i) eqn:LEdk; last first.
              {
                apply negbT in LEdk; rewrite -ltnNge in LEdk.
                apply leq_trans with (n := 0); last by done.
                apply leq_trans with (n := job_interference job_cost rate sched j_i j_fst
                                                                        (a_fst + R_k) t2).
                {
                  apply extend_sum; last by apply leqnn.
                  rewrite -(leq_add2r D_i).
                  rewrite interference_bound_edf_j_fst_deadline
                          interference_bound_edf_j_i_deadline in LEdl.
                  apply leq_trans with (n := a_fst + D_k); last by done.
                  rewrite -addnA leq_add2l.
                  by apply ltnW; rewrite -ltn_subRL.
                }
                apply leq_trans with (n := service_during rate sched j_fst (a_fst + R_k) t2);
                  first by apply job_interference_le_service; ins; rewrite H_rate_equals_one.
                unfold service_during; rewrite leqn0; apply/eqP.
                by apply cumulative_service_after_job_rt_zero with (job_cost0 := job_cost) (R := R_k);
                  try (by done); apply leqnn.
              }
              {
                rewrite -(leq_add2r (D_k - R_k)) subh1 // -addnBA // subnn addn0.
                assert (SUBST: D_k - R_k = \sum_(a_fst + R_k <= i < a_fst + D_k) 1).
                {
                  rewrite big_const_nat iter_addn mul1n addn0.
                  rewrite addnC -subnBA; last by apply leq_addr.
                  by rewrite addnC -addnBA // subnn addn0.
                }
                apply leq_trans with (n := job_interference job_cost rate sched j_i j_fst t1
                                                            (a_fst + D_k) + (D_k - R_k)).
                {
                  rewrite leq_add2r.
                  destruct (t2 <= a_fst + R_k) eqn:LEt2.
                  {
                    apply extend_sum; first by apply leqnn.
                    apply leq_trans with (n := a_fst + R_k); first by done.
                    by rewrite leq_add2l; apply H_R_k_le_deadline.
                  }
                  {
                    unfold job_interference.
                    apply negbT in LEt2; rewrite -ltnNge in LEt2.
                    rewrite -> big_cat_nat with (n := a_fst + R_k);
                      [simpl | by apply AFTERt1 | by apply ltnW].
                    apply leq_trans with (n := job_interference job_cost rate sched j_i j_fst t1
                                 (a_fst + R_k) + service_during rate sched j_fst (a_fst + R_k) t2).
                    {
                      rewrite leq_add2l.
                      by apply job_interference_le_service; ins; rewrite H_rate_equals_one.
                    }
                    unfold service_during.
                    rewrite -> cumulative_service_after_job_rt_zero with (job_cost0 := job_cost)
                                                                                     (R := R_k);
                      try (by done); last by apply leqnn.
                    rewrite addn0; apply extend_sum; first by apply leqnn.
                    by rewrite leq_add2l; apply H_R_k_le_deadline.
                  }
                }

                unfold job_interference.
                rewrite -> big_cat_nat with (n := a_fst + R_k);
                  [simpl| by apply AFTERt1 | by rewrite leq_add2l; apply H_R_k_le_deadline].
                apply leq_trans with (n := job_interference job_cost rate sched j_i j_fst t1
                  (a_fst+R_k) + service_during rate sched j_fst (a_fst+R_k) (a_fst+D_k) + (D_k-R_k)).
                {
                  rewrite leq_add2r leq_add2l.
                  by apply job_interference_le_service; ins; rewrite H_rate_equals_one.
                }
                unfold service_during.
                rewrite -> cumulative_service_after_job_rt_zero with (job_cost0 := job_cost) (R:=R_k);
                  try (by done); last by apply leqnn.
                rewrite addn0.
                apply leq_trans with (n := (\sum_(t1 <= t < a_fst + R_k) 1) +
                                           \sum_(a_fst + R_k <= t < a_fst + D_k) 1).
                {
                  apply leq_add; last by rewrite SUBST.
                  by unfold job_interference; apply leq_sum; ins; apply leq_b1.
                }
                rewrite -big_cat_nat;
                  [simpl | by apply AFTERt1 | by rewrite leq_add2l; apply H_R_k_le_deadline ].
                rewrite big_const_nat iter_addn mul1n addn0 leq_subLR.
                by unfold D_i, D_k, t1, a_fst; rewrite -interference_bound_edf_j_fst_deadline
                                                       -interference_bound_edf_j_i_deadline.
              }    
            Qed.

          End ResponseTimeOfSingleJobBounded.

          (* Else, if j_fst did not complete by its response-time bound, then
             we need a separate proof. *)
          Section ResponseTimeOfSingleJobNotBounded.

            Hypothesis H_j_fst_not_complete_by_rt_bound :
              ~~ completed job_cost rate sched j_fst (a_fst + R_k).

            (* This of course implies that a_fst + R_k lies after the end of the interval,
               otherwise j_fst would have completed by its response-time bound. *)
            Lemma interference_bound_edf_response_time_bound_of_j_fst_after_interval :
              job_arrival j_fst + R_k >= job_arrival j_i + delta.
            Proof.
              have FST := interference_bound_edf_j_fst_is_job_of_tsk_k.
              destruct FST as [FSTtask _].            
              rewrite leqNgt; apply/negP; intro LT.
              move: H_j_fst_not_complete_by_rt_bound => /negP BUG; apply BUG.
              by apply H_all_previous_jobs_completed_on_time.
            Qed.

            (* If the slack is too big (D_i < D_k - R_k), j_fst causes no interference. *)
            Lemma interference_bound_edf_holds_for_single_job_with_big_slack :
              D_i < D_k - R_k ->
              interference_caused_by j_fst t1 t2 = 0.
            Proof.
              intro LTdk.
              rewrite ltn_subRL in LTdk.
              rewrite -(ltn_add2l a_fst) addnA in LTdk.
              apply leq_ltn_trans with (m := t1 + D_i) in LTdk; last first.
              {
                rewrite leq_add2r.
                apply leq_trans with (n := t1 + delta); first by apply leq_addr.
                by apply interference_bound_edf_response_time_bound_of_j_fst_after_interval.
              }
              apply/eqP; rewrite -[_ _ _ _ == 0]negbK; apply/negP; red; intro BUG.
              apply interference_under_edf_implies_shorter_deadlines in BUG.
              rewrite interference_bound_edf_j_fst_deadline
                      interference_bound_edf_j_i_deadline in BUG.
              by apply (leq_trans LTdk) in BUG; rewrite ltnn in BUG.
            Qed.

            (* Else, if the slack is small, j_fst causes interference no longer than
               D_i - (D_k - R_k). *)
            Lemma interference_bound_edf_holds_for_single_job_with_small_slack :
              D_i >= D_k - R_k ->
              interference_caused_by j_fst t1 t2 <= D_i - (D_k - R_k).
            Proof.
              intro LEdk.
              have FST := interference_bound_edf_j_fst_is_job_of_tsk_k.
              destruct FST as [FSTtask [LEdl _]].            
              have LTr := interference_bound_edf_response_time_bound_of_j_fst_after_interval.
              apply subh3; last by apply LEdk.
              apply leq_trans with (n := job_interference job_cost rate sched j_i j_fst t1
                                                          (job_arrival j_fst + R_k) + (D_k - R_k));
                first by rewrite leq_add2r; apply extend_sum; [by apply leqnn|]. 
              apply leq_trans with (n := \sum_(t1 <= t < a_fst + R_k) 1 +
                                         \sum_(a_fst + R_k <= t < a_fst + D_k)1).
              {
                apply leq_add; unfold job_interference;
                  first by apply leq_sum; ins; apply leq_b1.
                rewrite big_const_nat iter_addn mul1n addn0 addnC.
                rewrite -subnBA; last by apply leq_addr.
                by rewrite addnC -addnBA // subnn addn0.
              }
              rewrite -big_cat_nat; simpl; last 2 first.
              {
                apply leq_trans with (n := t1 + delta); first by apply leq_addr.
                by apply interference_bound_edf_response_time_bound_of_j_fst_after_interval.
              }  
              by rewrite leq_add2l; apply H_R_k_le_deadline.
              rewrite big_const_nat iter_addn mul1n addn0 leq_subLR.
              unfold D_i, D_k, t1, a_fst; rewrite -interference_bound_edf_j_fst_deadline
                                                  -interference_bound_edf_j_i_deadline.
              by apply interference_under_edf_implies_shorter_deadlines in LEdl.
            Qed.

          End ResponseTimeOfSingleJobNotBounded.
          
          (* Finally, we prove that the interference caused by the single job
             is bounded by D_i - (D_k - R_k). *)
          Lemma interference_bound_edf_interference_of_j_fst_limited_by_slack :
            interference_caused_by j_fst t1 t2 <= D_i - (D_k - R_k).
          Proof.
            destruct (completed job_cost rate sched j_fst (a_fst + R_k)) eqn:COMP;
              first by apply interference_bound_edf_holds_for_single_job_that_completes_on_time. 
            apply negbT in COMP.
            destruct (ltnP D_i (D_k - R_k)) as [LEdk | LTdk].
              by rewrite interference_bound_edf_holds_for_single_job_with_big_slack.
              by apply interference_bound_edf_holds_for_single_job_with_small_slack.
          Qed.

          Lemma interference_bound_edf_holds_for_a_single_job :
            interference_caused_by j_fst t1 t2 <= interference_bound.
          Proof.
            rename H_many_jobs into NUM, H_only_one_job into SIZE.
            unfold interference_caused_by, interference_bound, edf_specific_interference_bound.
            fold D_i D_k p_k n_k.
            rewrite SIZE ltnS leqn0 in NUM; move: NUM => /eqP EQnk.
            rewrite EQnk mul0n add0n.
            rewrite leq_min; apply/andP; split.
            {
              apply interference_bound_edf_interference_le_task_cost.
              rewrite interference_bound_edf_job_in_same_sequence.
              by apply mem_nth; rewrite SIZE.
            }
            rewrite interference_bound_edf_simpl_when_there's_one_job.
            by apply interference_bound_edf_interference_of_j_fst_limited_by_slack.
          Qed.

        End InterferenceSingleJob.

        (* Next, consider the last case where there are at least two jobs:
           the first job j_fst, and the last job j_lst. *)
        Section InterferenceTwoOrMoreJobs.

          (* Assume there are at least two jobs. *)
          Variable num_mid_jobs: nat.
          Hypothesis H_at_least_two_jobs : size sorted_jobs = num_mid_jobs.+2.

          (* Let j_lst be the last job of the sequence and a_lst its arrival time. *)
          Let j_lst := nth elem sorted_jobs num_mid_jobs.+1.
          Let a_lst := job_arrival j_lst.

          (* In this section, we prove some basic lemmas about the first and last jobs. *)
          Section FactsAboutFirstAndLastJobs.

            (* The last job is an interfering job of task tsk_k. *)
            Lemma interference_bound_edf_j_lst_is_job_of_tsk_k :
              job_task j_lst = tsk_k /\
              interference_caused_by j_lst t1 t2 != 0 /\
              j_lst \in jobs_scheduled_between sched t1 t2.
            Proof.
              apply interference_bound_edf_all_jobs_from_tsk_k, mem_nth.
              by rewrite H_at_least_two_jobs.
            Qed.

            (* The deadline of j_lst is the deadline of tsk_k. *)
            Lemma interference_bound_edf_j_lst_deadline :
              job_deadline j_lst = task_deadline tsk_k.
            Proof.
              unfold valid_sporadic_job in *.
              rename H_valid_job_parameters into PARAMS.
              have LST := interference_bound_edf_j_lst_is_job_of_tsk_k.
              destruct LST as [LSTtask _].
              by specialize (PARAMS j_lst); des; rewrite PARAMS1 LSTtask.
            Qed.

            (* The first job arrives before the last job. *)
            Lemma interference_bound_edf_j_fst_before_j_lst :
              job_arrival j_fst <= job_arrival j_lst.
            Proof.
              rename H_at_least_two_jobs into SIZE.
              unfold j_fst, j_lst; rewrite -[num_mid_jobs.+1]add0n.
              apply prev_le_next; last by rewrite SIZE leqnn.
              by intros i LT; apply interference_bound_edf_jobs_ordered_by_arrival.
            Qed.

            (* The last job arrives before the end of the interval. *)
            Lemma interference_bound_edf_last_job_arrives_before_end_of_interval :
              job_arrival j_lst < t2.
            Proof.
              rename H_rate_equals_one into RATE.
              rewrite leqNgt; apply/negP; unfold not; intro LT2.
              exploit interference_bound_edf_all_jobs_from_tsk_k.
              {
                apply mem_nth; instantiate (1 := num_mid_jobs.+1).
                by rewrite -(ltn_add2r 1) addn1 H_at_least_two_jobs addn1.
              }  
              instantiate (1 := elem); move => [LSTtsk [/eqP LSTserv LSTin]].
              apply LSTserv; apply/eqP; rewrite -leqn0.
              apply leq_trans with (n := service_during rate sched j_lst t1 t2);
                first by apply job_interference_le_service; ins; rewrite RATE.
              rewrite leqn0; apply/eqP; unfold service_during.
              by apply cumulative_service_before_job_arrival_zero.
            Qed.

            (* Since there are multiple jobs, j_fst is far enough from the end of
               the interval so that its response-time bound is valid
               (by the assumption H_all_previous_jobs_completed_on_time). *)
            Lemma interference_bound_edf_j_fst_completed_on_time :
              completed job_cost rate sched j_fst (a_fst + R_k).
            Proof.
              have FST := interference_bound_edf_j_fst_is_job_of_tsk_k; des.
              set j_snd := nth elem sorted_jobs 1.
              exploit interference_bound_edf_all_jobs_from_tsk_k.
              {
                by apply mem_nth; instantiate (1 := 1); rewrite H_at_least_two_jobs.
              }
              instantiate (1 := elem); move => [SNDtsk [/eqP SNDserv _]].
              apply H_all_previous_jobs_completed_on_time; try (by done).
              apply leq_ltn_trans with (n := job_arrival j_snd); last first.
              {
                rewrite ltnNge; apply/negP; red; intro BUG; apply SNDserv.
                apply/eqP; rewrite -leqn0; apply leq_trans with (n := service_during rate
                                                                          sched j_snd t1 t2);
                  first by apply job_interference_le_service; ins; rewrite H_rate_equals_one.
                rewrite leqn0; apply/eqP.
                by apply cumulative_service_before_job_arrival_zero.
              }
              apply leq_trans with (n := a_fst + p_k).
              {
                by rewrite leq_add2l; apply leq_trans with (n := D_k);
                  [by apply H_R_k_le_deadline | by apply H_restricted_deadlines].
              }
            
              (* Since jobs are sporadic, we know that the first job arrives
                 at least p_k units before the second. *)
              unfold p_k; rewrite -FST.
              apply H_sporadic_tasks; [| by rewrite SNDtsk | ]; last first.
              {
                apply interference_bound_edf_jobs_ordered_by_arrival.
                by rewrite H_at_least_two_jobs.
              }
              red; move => /eqP BUG.
              by rewrite nth_uniq in BUG; rewrite ?SIZE //;
                [ by apply interference_bound_edf_at_least_one_job
                | by rewrite H_at_least_two_jobs
                | by rewrite sort_uniq; apply filter_uniq, undup_uniq].
            Qed.

          End FactsAboutFirstAndLastJobs.

          (* Next, we prove that the distance between the first and last jobs is at least
             num_mid_jobs + 1 periods. *)
          Lemma interference_bound_edf_many_periods_in_between :
            a_lst - a_fst >= num_mid_jobs.+1 * p_k.
          Proof.
            unfold a_fst, a_lst, j_fst, j_lst. 
            assert (EQnk: num_mid_jobs.+1=(size sorted_jobs).-1).
              by rewrite H_at_least_two_jobs.
            rewrite EQnk telescoping_sum;
              last by ins; apply interference_bound_edf_jobs_ordered_by_arrival.
            rewrite -[_ * _ tsk_k]addn0 mulnC -iter_addn -{1}[_.-1]subn0 -big_const_nat. 
            rewrite big_nat_cond [\sum_(0 <= i < _)(_-_)]big_nat_cond.
            apply leq_sum; intros i; rewrite andbT; move => /andP LT; des.

            (* To simplify, call the jobs 'cur' and 'next' *)
            set cur := nth elem sorted_jobs i.
            set next := nth elem sorted_jobs i.+1.

            (* Show that cur arrives earlier than next *)
            assert (ARRle: job_arrival cur <= job_arrival next).
              by unfold cur, next; apply interference_bound_edf_jobs_ordered_by_arrival.
             
            (* Show that both cur and next are in the arrival sequence *)
            assert (INnth: cur \in interfering_jobs /\ next \in interfering_jobs).
            {
              rewrite 2!interference_bound_edf_job_in_same_sequence; split.
                by apply mem_nth, (ltn_trans LT0); destruct sorted_jobs; ins.
                by apply mem_nth; destruct sorted_jobs; ins.
            }
            rewrite 2?mem_filter in INnth; des.

            (* Use the sporadic task model to conclude that cur and next are separated
               by at least (task_period tsk) units. Of course this only holds if cur != next.
               Since we don't know much about the list (except that it's sorted), we must
               also prove that it doesn't contain duplicates. *)
            assert (CUR_LE_NEXT: job_arrival cur + task_period (job_task cur) <= job_arrival next).
            {
              apply H_sporadic_tasks; last by ins.
              unfold cur, next, not; intro EQ; move: EQ => /eqP EQ.
              rewrite nth_uniq in EQ; first by move: EQ => /eqP EQ; intuition.
                by apply ltn_trans with (n := (size sorted_jobs).-1); destruct sorted_jobs; ins.
                by destruct sorted_jobs; ins.
                by rewrite sort_uniq -/interfering_jobs filter_uniq // undup_uniq.
                by move: INnth INnth0 => /eqP INnth /eqP INnth0; rewrite INnth INnth0.  
            }
            by rewrite subh3 // addnC; move: INnth => /eqP INnth; rewrite -INnth.
          Qed.

          (* Then, we prove that the ratio n_k is at least the number of middle jobs + 1, ... *)
          Lemma interference_bound_edf_n_k_covers_middle_jobs_plus_one :
            n_k >= num_mid_jobs.+1.
          Proof.
            rename H_valid_task_parameters into TASK_PARAMS,
                   H_tsk_k_in_task_set into INk.
            unfold valid_sporadic_taskset, is_valid_sporadic_task,
                   interference_bound, edf_specific_interference_bound in *.
            have DIST := interference_bound_edf_many_periods_in_between.
            have AFTERt1 :=
                interference_bound_edf_j_fst_completion_implies_rt_bound_inside_interval
                interference_bound_edf_j_fst_completed_on_time.
            rewrite leqNgt; apply/negP; unfold not; intro LTnk; unfold n_k in LTnk.
            rewrite ltn_divLR in LTnk; last by specialize (TASK_PARAMS tsk_k INk); des.
            apply (leq_trans LTnk) in DIST; rewrite ltn_subRL in DIST.
            rewrite -(ltn_add2r D_k) -addnA [D_i + _]addnC addnA in DIST. 
            apply leq_ltn_trans with (m := job_arrival j_i + D_i) in DIST; last first.
            {
              rewrite leq_add2r; apply (leq_trans AFTERt1).
              by rewrite leq_add2l; apply H_R_k_le_deadline.
            }
            have LST := interference_bound_edf_j_lst_is_job_of_tsk_k.
            destruct LST as [_ [ LEdl _]].  
            apply interference_under_edf_implies_shorter_deadlines in LEdl.
            unfold D_i, D_k in DIST; rewrite interference_bound_edf_j_lst_deadline
                                             interference_bound_edf_j_i_deadline in LEdl.
            by rewrite ltnNge LEdl in DIST.
          Qed.

          (* ... which allows bounding the interference of the middle and last jobs
             using n_k multiplied by the cost. *)
          Lemma interference_bound_edf_holds_for_middle_and_last_jobs :
            interference_caused_by j_lst t1 t2 +
              \sum_(0 <= i < num_mid_jobs)
                interference_caused_by (nth elem sorted_jobs i.+1) t1 t2
            <= n_k * task_cost tsk_k.
          Proof.
            apply leq_trans with (n := num_mid_jobs.+1 * task_cost tsk_k); last first.
            {
              rewrite leq_mul2r; apply/orP; right.
              by apply interference_bound_edf_n_k_covers_middle_jobs_plus_one.
            }
            rewrite mulSn; apply leq_add.
            {
              apply interference_bound_edf_interference_le_task_cost.
              rewrite interference_bound_edf_job_in_same_sequence.
              by apply mem_nth; rewrite H_at_least_two_jobs.
            }
            {
              apply leq_trans with (n := \sum_(0 <= i < num_mid_jobs) task_cost tsk_k);
                last by rewrite big_const_nat iter_addn addn0 mulnC subn0.
              rewrite big_nat_cond [\sum_(0 <= i < num_mid_jobs) task_cost _]big_nat_cond.
              apply leq_sum; intros i; rewrite andbT; move => /andP LT; des.
              apply interference_bound_edf_interference_le_task_cost.
              rewrite interference_bound_edf_job_in_same_sequence.
              apply mem_nth; rewrite H_at_least_two_jobs.
              by rewrite ltnS; apply leq_trans with (n := num_mid_jobs).
            }
          Qed.

          (* Since n_k < sorted_jobs = num_mid_jobs + 2, it follows that
             n_k = num_mid_jobs + 1. *)
          Lemma interference_bound_edf_n_k_equals_num_mid_jobs_plus_one :
            n_k = num_mid_jobs.+1.
          Proof.
            rename H_many_jobs into NUM, H_at_least_two_jobs into SIZE.
            have NK := interference_bound_edf_n_k_covers_middle_jobs_plus_one.
            move: NK; rewrite leq_eqVlt orbC; move => /orP NK; des;
             first by rewrite SIZE ltnS leqNgt NK in NUM.
            by move: NK => /eqP NK; rewrite NK. 
          Qed.
          
          (* The interference bound of the first job must be proven separately,
             since it exploits the slack. *)
          Section InterferenceOfFirstJob.

            (* In order to move (D_i %% p_k) to the other side of the inequality,
               we need to prove it is no larger than the slack. *)
            Lemma interference_bound_edf_remainder_ge_slack :
              D_k - R_k <= D_i %% p_k.
            Proof.
              have AFTERt1 :=
                interference_bound_edf_j_fst_completion_implies_rt_bound_inside_interval
                interference_bound_edf_j_fst_completed_on_time.
              have NK := interference_bound_edf_n_k_equals_num_mid_jobs_plus_one.
              have DIST := interference_bound_edf_many_periods_in_between.
              rewrite -NK in DIST.
              rewrite -subndiv_eq_mod leq_subLR.
              fold (div_floor D_i p_k) n_k.
              rewrite addnBA; last by apply leq_trunc_div.
              apply leq_trans with (n := R_k + D_i - (a_lst - a_fst)); last by apply leq_sub2l.
              rewrite subnBA; last by apply interference_bound_edf_j_fst_before_j_lst.
              rewrite -(leq_add2r a_lst) subh1; last first.
              {
                apply leq_trans with (n := t2);
                  [by apply ltnW, interference_bound_edf_last_job_arrives_before_end_of_interval|].
                rewrite addnC addnA.
                apply leq_trans with (n := t1 + D_i).
                  unfold t2; rewrite leq_add2l; apply H_delta_le_deadline.
                by rewrite leq_add2r; apply AFTERt1.
              }
              rewrite -addnBA // subnn addn0 [D_k + _]addnC.
              apply leq_trans with (n := t1 + D_i);
                last by rewrite -addnA [D_i + _]addnC addnA leq_add2r addnC AFTERt1.
              have LST := interference_bound_edf_j_lst_is_job_of_tsk_k.
              destruct LST as [_ [ LSTserv _]].
              unfold D_i, D_k, a_lst, t1; rewrite -interference_bound_edf_j_lst_deadline
                                                  -interference_bound_edf_j_i_deadline.
              by apply interference_under_edf_implies_shorter_deadlines in LSTserv.
            Qed.

            (* To help with the last lemma, we prove that interference caused by j_fst
               is bounded by the length of the interval [t1, a_fst + R_k), ... *)
            Lemma interference_bound_edf_interference_of_j_fst_bounded_by_response_time :
               interference_caused_by j_fst t1 t2 <= \sum_(t1 <= t < a_fst + R_k) 1.
            Proof.
              assert (AFTERt1: t1 <= a_fst + R_k).
              {
                apply interference_bound_edf_j_fst_completion_implies_rt_bound_inside_interval.
                by apply interference_bound_edf_j_fst_completed_on_time.
              }
              destruct (leqP t2 (a_fst + R_k)) as [LEt2 | GTt2].
              {
                apply leq_trans with (n := job_interference job_cost rate sched j_i j_fst t1
                                                                              (a_fst + R_k));
                  first by apply extend_sum; rewrite ?leqnn.
                by apply leq_sum; ins; rewrite leq_b1.
              }
              {
                unfold interference_caused_by, job_interference.
                rewrite -> big_cat_nat with (n := a_fst + R_k);
                  [simpl | by apply AFTERt1 | by apply ltnW].
                rewrite -[\sum_(_ <= _ < _) 1]addn0; apply leq_add;
                  first by apply leq_sum; ins; apply leq_b1.
                apply leq_trans with (n := service_during rate sched j_fst (a_fst + R_k) t2);
                  first by apply job_interference_le_service; ins; rewrite H_rate_equals_one.
                rewrite leqn0; apply/eqP.
                apply cumulative_service_after_job_rt_zero with (job_cost0 := job_cost) (R := R_k);
                  [ by done | | by apply leqnn].
                by apply interference_bound_edf_j_fst_completed_on_time.
              }
            Qed.

            (* ..., that we can bound the terms in the inequality using interval lengths,... *)
            Lemma interference_bound_edf_bounding_interference_with_interval_lengths :
              interference_caused_by j_fst t1 t2 + (D_k - R_k) + D_i %/ p_k * p_k <=
              \sum_(t1 <= t < a_fst + R_k) 1
              + \sum_(a_fst + R_k <= t < a_fst + D_k) 1
              + \sum_(a_fst + D_k <= t < a_lst + D_k) 1.
            Proof.
              apply leq_trans with (n := \sum_(t1 <= t < a_fst + R_k) 1 + (D_k - R_k) +
                                                                       D_i %/ p_k * p_k).
              {
                rewrite 2!leq_add2r.
                apply interference_bound_edf_interference_of_j_fst_bounded_by_response_time.
              }
              apply leq_trans with (n := \sum_(t1 <= t < a_fst + R_k) 1 + (D_k - R_k) +
                                                                        (a_lst - a_fst)).
              {
                rewrite leq_add2l; fold (div_floor D_i p_k) n_k.
                rewrite interference_bound_edf_n_k_equals_num_mid_jobs_plus_one.
                by apply interference_bound_edf_many_periods_in_between.
              }
              apply leq_trans with (n := \sum_(t1 <= t < a_fst + R_k) 1 +
                  \sum_(a_fst + R_k <= t < a_fst + D_k) 1 + \sum_(a_fst + D_k <= t < a_lst + D_k) 1).
              {
                by rewrite -2!addnA leq_add2l; apply leq_add;
                rewrite big_const_nat iter_addn mul1n addn0;
                rewrite ?subnDl ?subnDr leqnn.
              }
              by apply leqnn.
            Qed.

            (*..., and that the concatenation of these interval lengths equals (a_lst + D_k) - 1. *)
            Lemma interference_bound_edf_simpl_by_concatenation_of_intervals :
              \sum_(t1 <= t < a_fst + R_k) 1
              + \sum_(a_fst + R_k <= t < a_fst + D_k) 1
              + \sum_(a_fst + D_k <= t < a_lst + D_k) 1 = (a_lst + D_k) - t1.
            Proof.
              assert (AFTERt1: t1 <= a_fst + R_k).
              {
                apply interference_bound_edf_j_fst_completion_implies_rt_bound_inside_interval.
                by apply interference_bound_edf_j_fst_completed_on_time.
              }
              rewrite -big_cat_nat;
                [simpl | by apply AFTERt1 | by rewrite leq_add2l; apply H_R_k_le_deadline].
              rewrite -big_cat_nat; simpl; last 2 first.
              {
                apply leq_trans with (n := a_fst + R_k); first by apply AFTERt1.
                by rewrite leq_add2l; apply H_R_k_le_deadline.
              }
              {
                rewrite leq_add2r; unfold a_fst, a_lst, j_fst, j_lst.
                rewrite -[num_mid_jobs.+1]add0n; apply prev_le_next;
                  last by rewrite add0n H_at_least_two_jobs ltnSn.
                by ins; apply interference_bound_edf_jobs_ordered_by_arrival.
              }
              by rewrite big_const_nat iter_addn mul1n addn0.
            Qed.
            
            (* Using the fact that absolute deadlines are ordered, we show that the
               interference caused by the first job is no larger than D_i %% p_k - (D_k - R_k). *)
            Lemma interference_bound_edf_interference_of_j_fst_limited_by_remainder_and_slack :
              interference_caused_by j_fst t1 t2 <= D_i %% p_k - (D_k - R_k).
            Proof.
              assert (AFTERt1: t1 <= a_fst + R_k).
              {
                apply interference_bound_edf_j_fst_completion_implies_rt_bound_inside_interval.
                by apply interference_bound_edf_j_fst_completed_on_time.
              }
              apply subh3; last by apply interference_bound_edf_remainder_ge_slack.
              rewrite -subndiv_eq_mod; apply subh3; last by apply leq_trunc_div.
              apply (leq_trans interference_bound_edf_bounding_interference_with_interval_lengths).
              rewrite interference_bound_edf_simpl_by_concatenation_of_intervals leq_subLR.
              have LST := interference_bound_edf_j_lst_is_job_of_tsk_k.
              destruct LST as [_ [ LSTserv _]].
              unfold D_i, D_k, a_lst, t1; rewrite -interference_bound_edf_j_lst_deadline
                                                  -interference_bound_edf_j_i_deadline.
              by apply interference_under_edf_implies_shorter_deadlines in LSTserv.
            Qed.

          End InterferenceOfFirstJob.
          
        End InterferenceTwoOrMoreJobs.

      End InterferenceManyJobs.
      
      Theorem interference_bound_edf_bounds_interference :
        x <= interference_bound.
      Proof.
        (* Use the definition of workload based on list of jobs. *)
        rewrite interference_bound_edf_use_another_definition. 

        (* We only care about the jobs that cause interference. *)
        rewrite interference_bound_edf_simpl_by_filtering_interfering_jobs.

        (* Now we order the list by job arrival time. *)
        rewrite interference_bound_edf_simpl_by_sorting_interfering_jobs.

        (* Next, we show that the workload bound holds if n_k
           is no larger than the number of interferings jobs. *)
        destruct (size sorted_jobs <= n_k) eqn:NUM;
          first by apply interference_bound_edf_holds_for_at_most_n_k_jobs.
        apply negbT in NUM; rewrite -ltnNge in NUM.

        (* Find some dummy element to use in the nth function *)
        assert (EX: exists elem: JobIn arr_seq, True).
          destruct sorted_jobs as [| j]; [by rewrite ltn0 in NUM | by exists j].
        destruct EX as [elem _].

        (* Now we index the sum to access the first and last elements. *)
        rewrite (big_nth elem).

        (* First, we show that the bound holds for an empty list of jobs. *)
        destruct (size sorted_jobs) as [| n] eqn:SIZE;
          first by rewrite big_geq.

        (* Then, we show the same for a singleton set of jobs. *)
        rewrite SIZE; destruct n as [| num_mid_jobs].
        {
          rewrite big_nat_recr // big_geq //.
          rewrite [nth]lock /= -lock add0n.
          by apply interference_bound_edf_holds_for_a_single_job; rewrite SIZE.
        }
        
        (* Knowing that we have at least two elements, we take first and last out of the sum *) 
        rewrite [nth]lock big_nat_recl // big_nat_recr // /= -lock.
        rewrite addnA addnC addnA.

        (* Recall that n_k >= num_mids_jobs + 1.
           Because num_mid_jobs < size_sorted_jobs < n_k, it follows that
           n_k = num_mid_jobs + 2 is the only possible case. *)
        exploit interference_bound_edf_n_k_equals_num_mid_jobs_plus_one;
          [by rewrite SIZE | by apply elem | by rewrite SIZE | intro NK].

        (* We use the lemmas we proved to show that the interference bound holds. *)
        unfold interference_bound, edf_specific_interference_bound.
        fold D_i D_k p_k n_k.
        rewrite addnC addnA; apply leq_add;
          first by rewrite addnC interference_bound_edf_holds_for_middle_and_last_jobs // SIZE.
        rewrite leq_min; apply/andP; split.
        {
          apply interference_bound_edf_interference_le_task_cost.
          rewrite interference_bound_edf_job_in_same_sequence.
          by apply mem_nth; rewrite SIZE.
        }
        by apply interference_bound_edf_interference_of_j_fst_limited_by_remainder_and_slack with
                                                    (num_mid_jobs := num_mid_jobs); rewrite SIZE.
      Qed.
      
    End MainProof.
    
  End ProofInterferenceBound.

End EDFSpecificBound.