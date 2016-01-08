Require Import Vbase task job task_arrival schedule platform interference
        workload workload_bound schedulability priority response_time
        bertogna_fp_theory util_divround util_lemmas
        ssreflect ssrbool eqtype ssrnat seq fintype bigop div path.

  (* In the following section, we define Bertogna and Cirinei's
     EDF-specific per-task interference bound. *)
Module EDFSpecificBound.

  Import Job SporadicTaskset ScheduleOfSporadicTask Workload Schedulability ResponseTime
         Priority SporadicTaskArrival.

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

    (* and j_i one of its jobs. *)
    Variable j_i: JobIn arr_seq.
    Hypothesis H_job_of_tsk_i: job_task j_i = tsk_i.

    (* Let tsk_k denote any interfering task, and R_k its response-time bound. *)
    Variable tsk_k: sporadic_task.
    Variable R_k: time.
    
    (* Consider a time window of length delta, starting with j_i's arrival time. *)
    Variable delta: time.

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

      Print edf_specific_interference_bound.
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
        Lemma interference_bound_edf_bound_simpl_by_sorting_interfering_jobs :
          \sum_(j <- interfering_jobs) interference_caused_by j t1 t2 =
           \sum_(j <- sorted_jobs) interference_caused_by j t1 t2.
        Proof.
          by rewrite (eq_big_perm sorted_jobs) /=; last by rewrite -(perm_sort order).
        Qed.

        (* Remember that both sequences have the same set of elements *)
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

        (* Remember that for any job of tsk, service <= task_cost tsk *)
        (*assert (LTserv: forall j (INi: j \in interfering_jobs),
                          job_interference job_cost rate sched j_i j t1 t2 <= task_cost tsk_k).
        {
          intros j; rewrite mem_filter; move => /andP [/andP [/eqP JOBj _] _].
          specialize (PARAMS j); des.
          apply leq_trans with (n := service_during rate sched j t1 t2);
            first by apply job_interference_le_service; ins; rewrite RATE.
          by apply cumulative_service_le_task_cost with (job_task0 := job_task) (task_deadline0 := task_deadline) (job_cost0 := job_cost) (job_deadline0 := job_deadline).
        }*)

      End SimplifyJobSequence.

      (* Next, we show that if the number of jobs is no larger than n_k,
         the workload bound trivially holds. *)
      Section WorkloadNotManyJobs.

        (*Lemma workload_bound_holds_for_at_most_n_k_jobs :
          size sorted_jobs <= n_k ->
          \sum_(i <- sorted_jobs) service_during rate sched i t1 t2 <=
            workload_bound.
        Proof.
        intros LEnk.
        rewrite -[\sum_(_ <- _ | _) _]add0n leq_add //.
        apply leq_trans with (n := \sum_(x <- sorted_jobs) task_cost tsk);
          last by rewrite big_const_seq iter_addn addn0 mulnC leq_mul2r; apply/orP; right.
        {
          rewrite [\sum_(_ <- _) service_during _ _ _ _ _]big_seq_cond.
          rewrite [\sum_(_ <- _) task_cost _]big_seq_cond.
          apply leq_sum; intros j_i; move/andP => [INi _].
          apply workload_bound_all_jobs_from_tsk in INi; des. 
          eapply cumulative_service_le_task_cost;
            [by apply H_completed_jobs_dont_execute | by apply INi |].
          by apply H_jobs_have_valid_parameters.
        }
      Qed.*)

      End WorkloadNotManyJobs.
    
      Theorem interference_bound_edf_bounds_interference :
        x <= interference_bound.
      Proof.
        (*rename H_jobs_have_valid_parameters into job_properties,
               H_no_deadline_misses_during_interval into no_dl_misses,
               H_valid_task_parameters into task_properties.
        unfold valid_sporadic_job, valid_realtime_job, restricted_deadline_model,
               valid_sporadic_taskset, is_valid_sporadic_task, sporadic_task_model,
               workload_of, no_deadline_misses_by, workload_bound, W in *; ins; des.
        fold n_k.*)

        unfold x.

        (* Use the definition of workload based on list of jobs. *)
        rewrite workload_eq_workload_joblist; unfold workload_joblist.

        (* We only care about the jobs that cause interference. *)
        rewrite workload_bound_simpl_by_filtering_interfering_jobs.

        (* Now we order the list by job arrival time. *)
        rewrite workload_bound_simpl_by_sorting_interfering_jobs.

        (* Next, we show that the workload bound holds if n_k
           is no larger than the number of interferings jobs. *)
        destruct (size sorted_jobs <= n_k) eqn:NUM;
          first by apply workload_bound_holds_for_at_most_n_k_jobs.
        apply negbT in NUM; rewrite -ltnNge in NUM.

        (* Find some dummy element to use in the nth function *)
        assert (EX: exists elem: JobIn arr_seq, True).
          destruct sorted_jobs; [ by rewrite ltn0 in NUM | by exists j].
        destruct EX as [elem _].

        (* Now we index the sum to access the first and last elements. *)
        rewrite (big_nth elem).

        (* First, we show that the bound holds for an empty list of jobs. *)
        destruct (size sorted_jobs) as [| n] eqn:SIZE;
          first by rewrite big_geq.
        
        (* Then, we show the same for a singleton set of jobs. *)
        destruct n as [| num_mid_jobs];
          first by apply workload_bound_holds_for_a_single_job; rewrite SIZE.

        admit.
      Qed.

    End MainProof.
    
  End ProofInterferenceBound.

End EDFSpecificBound.
  

(*          unfold valid_sporadic_taskset, is_valid_sporadic_task, valid_sporadic_job in *.
          intros tsk_k R_k INBOUNDSk.
          rename R' into R_i.
          unfold x; destruct ((tsk_k \in ts) && is_interfering_task_jlfp tsk' tsk_k) eqn:INTERFk;
            last by done.
          move: INTERFk => /andP [INk INTERFk].
          unfold edf_specific_bound; simpl.

          rename j' into j_i, tsk' into tsk_i.

          rewrite interference_eq_interference_joblist; last by done.
          unfold task_interference_joblist.

    

        assert (PRIOinterf:
                  forall (j j': JobIn arr_seq) t1 t2,
                    job_interference job_cost rate sched j' j t1 t2 != 0 ->
                    job_arrival j + job_deadline j <= job_arrival j' + job_deadline j').
        {
          clear - t1 t2 INVARIANT; clear t1 t2.
          intros j j' t1 t2 INTERF.
          unfold job_interference in INTERF.
          destruct ([exists t': 'I_t2, (t' >= t1) && backlogged job_cost rate sched j' t' && scheduled sched j t']) eqn:EX.
          {
            move: EX => /existsP EX; destruct EX as [t' EX];move: EX => /andP [/andP [LE BACK] SCHED].
            eapply interfering_job_has_higher_eq_prio in BACK;
              [ | by apply INVARIANT | by apply SCHED].
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
        }
        
        (* Find some dummy element to use in the nth function *)
        destruct (size sorted_jobs == 0) eqn:SIZE0;
          first by move: SIZE0 =>/eqP SIZE0; rewrite (size0nil SIZE0) big_nil.
        apply negbT in SIZE0; rewrite -lt0n in SIZE0.
        assert (EX: exists elem: JobIn arr_seq, True); des.
          destruct sorted_jobs; [by rewrite ltn0 in SIZE0 | by exists s].
        clear EX SIZE0.

        (* Remember that the jobs are ordered by arrival. *)
        assert (ALL: forall i (LTsort: i < (size sorted_jobs).-1),
                       order (nth elem sorted_jobs i) (nth elem sorted_jobs i.+1)).
        by destruct sorted_jobs; [by ins| by apply/pathP; apply SORT].
        
        (* Now we start the proof. First, we show that the workload bound
           holds if n_k is no larger than the number of interferings jobs. *)
        destruct (size sorted_jobs <= n_k) eqn:NUM.
        {
          rewrite -[\sum_(_ <- _ | _) _]addn0 leq_add //.
          apply leq_trans with (n := \sum_(x <- sorted_jobs) task_cost tsk_k);
            last by rewrite big_const_seq iter_addn addn0 mulnC leq_mul2r; apply/orP; right.
          {
            rewrite [\sum_(_ <- _) job_interference _  _ _ _ _ _ _]big_seq_cond.
            rewrite [\sum_(_ <- _) task_cost _]big_seq_cond.
            by apply leq_sum; intros j; rewrite andbT; intros INj; apply LTserv; rewrite INboth.
          }
        }
        apply negbT in NUM; rewrite -ltnNge in NUM.

        (* Now we index the sum to access the first and last elements. *)
        rewrite (big_nth elem).

        (* First and last only exist if there are at least 2 jobs. Thus, we must show
           that the bound holds for the empty list. *)
        destruct (size sorted_jobs) eqn:SIZE; first by rewrite big_geq.
        rewrite SIZE.
        
        (* Let's derive some properties about the first element. *)
        exploit (mem_nth elem); last intros FST.
          by instantiate (1:= sorted_jobs); instantiate (1 := 0); rewrite SIZE.
        move: FST; rewrite -INboth mem_filter; move => /andP FST; des.
        move: FST => /andP FST; des; move: FST => /eqP FST.
        rename FST0 into FSTin, FST into FSTtask, FST1 into FSTserv.       
                                  
        (* Now we show that the bound holds for a singleton set of interfering jobs. *)
        set j_fst := (nth elem sorted_jobs 0).
        set a_fst := job_arrival j_fst.

        assert (DLfst: job_deadline j_fst = task_deadline tsk_k).
        {
          by specialize (PARAMS j_fst); des; rewrite PARAMS1 FSTtask.
        }

        assert (DLi: job_deadline j_i = task_deadline tsk_i).
        {
          by specialize (PARAMS j_i); des; rewrite PARAMS1 JOBtsk.
        }

        assert (AFTERt1: completed job_cost rate sched j_fst (a_fst + R_k) -> t1 <= a_fst + R_k).
        {
          intros RBOUND.
          rewrite leqNgt; apply/negP; unfold not; intro BUG.
          move: FSTserv => /negP FSTserv; apply FSTserv.
          rewrite -leqn0; apply leq_trans with (n := service_during rate sched j_fst t1 t2);
            first by apply job_interference_le_service; ins; rewrite RATE.
          rewrite leqn0; apply/eqP.
          by apply cumulative_service_after_job_rt_zero with (job_cost0 := job_cost) (R := R_k); try (by done); apply ltnW.
        }

        assert (COMPok: completed job_cost rate sched j_fst (a_fst + R_k) -> job_interference job_cost rate sched j_i j_fst t1 t2 <= D_i - (D_k - R_k)).
        {
          intros RBOUND.
          apply PRIOinterf in FSTserv; rename FSTserv into LEdl.

          destruct (D_k - R_k <= D_i) eqn:LEdk; last first.
          {
            apply negbT in LEdk; rewrite -ltnNge in LEdk.
            apply leq_trans with (n := 0); last by done.
            apply leq_trans with (n := job_interference job_cost rate sched j_i j_fst
                                                        (a_fst + R_k) t2).
            {
              apply extend_sum; last by apply leqnn.
              rewrite -(leq_add2r D_i).
              rewrite DLi DLfst in LEdl.
              apply leq_trans with (n := a_fst + D_k); last by done.
              rewrite -addnA leq_add2l.
              by apply ltnW; rewrite -ltn_subRL.
            }
            apply leq_trans with (n := service_during rate sched j_fst (a_fst + R_k) t2);
              first by apply job_interference_le_service; ins; rewrite RATE.
            unfold service_during.
            by rewrite -> cumulative_service_after_job_rt_zero with (job_cost0 := job_cost) (R := R_k);
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
                by rewrite leq_add2l; apply NOMISS.
              }
              {
                unfold job_interference.
                apply negbT in LEt2; rewrite -ltnNge in LEt2.
                rewrite -> big_cat_nat with (n := a_fst + R_k);
                  [simpl | by apply AFTERt1 | by apply ltnW].
                apply leq_trans with (n := job_interference job_cost rate sched j_i j_fst t1
                                                                               (a_fst + R_k)
                                          + service_during rate sched j_fst (a_fst + R_k) t2).
                {
                  rewrite leq_add2l.
                  by apply job_interference_le_service; ins; rewrite RATE.
                }
                unfold service_during.
                rewrite -> cumulative_service_after_job_rt_zero with (job_cost0 := job_cost) (R := R_k);
                  try (by done); last by apply leqnn.
                rewrite addn0; apply extend_sum; first by apply leqnn.
                by rewrite leq_add2l; apply NOMISS.
              }
            }

            unfold job_interference.
            rewrite -> big_cat_nat with (n := a_fst + R_k);
              [simpl|by apply AFTERt1 | by rewrite leq_add2l; apply NOMISS].
            apply leq_trans with (n := job_interference job_cost rate sched j_i j_fst t1 (a_fst + R_k)
                                       + service_during rate sched j_fst (a_fst + R_k) (a_fst + D_k)
                                       + (D_k - R_k)).
            {
              rewrite leq_add2r leq_add2l.
              by apply job_interference_le_service; ins; rewrite RATE.
            }
            unfold service_during.
            rewrite -> cumulative_service_after_job_rt_zero with (job_cost0 := job_cost) (R := R_k);
              try (by done); last by apply leqnn.
            rewrite addn0.
            apply leq_trans with (n := (\sum_(t1 <= t < a_fst + R_k) 1) +
                                       \sum_(a_fst + R_k <= t < a_fst + D_k) 1).
            {
              apply leq_add; last by rewrite SUBST.
              by unfold job_interference; apply leq_sum; ins; apply leq_b1.
            }
            rewrite -big_cat_nat;
              [simpl | by apply AFTERt1 | by rewrite leq_add2l; apply NOMISS ].
            rewrite big_const_nat iter_addn mul1n addn0 leq_subLR.
            by unfold D_k, D_i, t2; rewrite -DLfst -DLi; apply LEdl.          
          }    
        }
        
        destruct n.
        {
          destruct n_k eqn:EQnk; last by ins.
          rewrite mul0n add0n big_nat_recl // big_geq // addn0; fold j_fst.
          rewrite leq_min; apply/andP; split;
            first by apply LTserv; rewrite INboth; apply/(nthP elem); exists 0; rewrite ?SIZE.
          move: EQnk => /eqP EQnk; unfold n_k, div_floor in EQnk.
          rewrite -leqn0 leqNgt divn_gt0 in EQnk;
            last by specialize (TASK_PARAMS tsk_k INk); des.
          rewrite -ltnNge in EQnk; rewrite modn_small //.

          destruct (job_arrival j_fst + R_k < job_arrival j_i + R_i) eqn:LTr.
          {
            exploit BEFOREok; [by apply FSTtask | by apply INBOUNDSk | by done |].
            by intros RBOUND;  apply COMPok in RBOUND.
          }

          (* Now we have the hard case: j_fst cannot use the IH and
             also has not completed within R_k time units. *)
          apply negbT in LTr; rewrite -leqNgt in LTr.
          apply PRIOinterf in FSTserv; rename FSTserv into LEdl.
          move: LEdl => LEdl; rewrite DLi DLfst in LEdl.

          destruct (D_k - R_k <= D_i) eqn:LEdk; last first.
          {
            apply negbT in LEdk; rewrite -ltnNge in LEdk.
            apply leq_trans with (n := 0); last by done.
            rewrite ltn_subRL in LEdk.
            rewrite -(ltn_add2l a_fst) addnA in LEdk.
            apply leq_ltn_trans with (m := t1 + D_i) in LEdk; last first.
            {
              rewrite leq_add2r.
              by apply leq_trans with (n := t1 + R_i); first by apply leq_addr.
            }
            rewrite leqn0 eqn0Ngt; apply/negP; rewrite lt0n; red; intro BUG.
            apply PRIOinterf in BUG; rewrite DLfst DLi in BUG.
            by apply (leq_ltn_trans BUG) in LEdk; rewrite ltnn in LEdk.
          }
          apply subh3; last by apply LEdk.
          
          apply leq_trans with (n := job_interference job_cost rate sched j_i j_fst t1 (job_arrival j_fst + R_k) + (D_k - R_k));
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
            by apply leq_trans with (n := t1 + R_i); first by apply leq_addr.
            by rewrite leq_add2l; apply NOMISS.
            by rewrite big_const_nat iter_addn mul1n addn0 leq_subLR LEdl. 
        } rewrite [nth]lock /= -lock in ALL.
    
        (* Knowing that we have at least two elements, we take first and last out of the sum *) 
        rewrite [nth]lock big_nat_recl // big_nat_recr // /= -lock.
        rewrite addnA addnC addnA.
        
        set j_lst := (nth elem sorted_jobs n.+1); fold j_fst.
                       
        (* Now we infer some facts about how first and last are ordered in the timeline *)
        assert (INfst: j_fst \in interfering_jobs).
          by unfold j_fst; rewrite INboth; apply mem_nth; destruct sorted_jobs; ins.

        assert (INlst: j_lst \in interfering_jobs).
          by unfold j_lst; rewrite INboth; apply mem_nth; rewrite SIZE.
        move: INlst; rewrite mem_filter; move => /andP [/andP [/eqP LSTtask LSTserv] LSTin].

        assert (DLlst: job_deadline j_lst = task_deadline tsk_k).
        {
          by specialize (PARAMS j_lst); des; rewrite PARAMS1 LSTtask.
        }

        assert (BEFOREarr: job_arrival j_fst <= job_arrival j_lst).
        {
          unfold j_fst, j_lst; rewrite -[n.+1]add0n.
          apply prev_le_next; last by rewrite add0n SIZE leqnn.
          by unfold order in ALL; intro i; rewrite SIZE; apply ALL.
        }

        assert (BEFOREt2: job_arrival j_lst < t2).
        {
          rewrite leqNgt; apply/negP; unfold not; intro LT2.
          assert (LTsize: n.+1 < size sorted_jobs).
            by destruct sorted_jobs; ins; rewrite SIZE; apply ltnSn.
          apply (mem_nth elem) in LTsize; rewrite -INboth in LTsize.
          rewrite -/interfering_jobs mem_filter in LTsize.
          move: LTsize => /andP [LTsize _]; des.
          move: LTsize => /andP [_ SERV].
          move: SERV => /eqP SERV; apply SERV.
          apply/eqP; rewrite -leqn0.
          apply leq_trans with (n := service_during rate sched j_lst t1 t2);
            first by apply job_interference_le_service; ins; rewrite RATE.
          rewrite leqn0; apply/eqP.
          by apply cumulative_service_before_job_arrival_zero.
        }

        assert (FSTok: completed job_cost rate sched j_fst (a_fst + R_k)).
        {
          set j_snd := nth elem sorted_jobs 1.
          assert (IN2: j_snd \in interfering_jobs).
            by rewrite INboth mem_nth // SIZE.
          rewrite mem_filter in IN2; move: IN2 => /andP [/andP [/eqP TSKsnd INTERF2] _].
          apply BEFOREok with (tsk := tsk_k); try (by done).
          apply leq_ltn_trans with (n := job_arrival j_snd); last first.
          {
            rewrite ltnNge; apply/negP; red; intro BUG.
            move: INTERF2 => /negP INTERF2; apply INTERF2.
            rewrite -leqn0; apply leq_trans with (n := service_during rate sched j_snd t1 t2);
              first by apply job_interference_le_service; ins; rewrite RATE.
            rewrite leqn0; apply/eqP.
            by apply cumulative_service_before_job_arrival_zero.
          }
          apply leq_trans with (n := a_fst + p_k).
          {
            rewrite leq_add2l.
            apply leq_trans with (n := D_k); first by apply NOMISS.
            by apply RESTR.
          }
          (* Since jobs are sporadic, we know that the first job arrives
             at least p_k units before the second. *)
          unfold p_k; rewrite -FSTtask.
          apply H_sporadic_tasks; [| by rewrite TSKsnd | by apply ALL].
          red; move => /eqP BUG.
          rewrite nth_uniq in BUG; rewrite ?SIZE //.
          by rewrite sort_uniq filter_uniq // undup_uniq //.
        }

        (* Now we upper-bound the service of the middle jobs. *)
        assert (BOUNDmid: \sum_(0 <= i < n)
                           job_interference job_cost rate sched j_i (nth elem sorted_jobs i.+1) t1 t2 <=
                             n * task_cost tsk_k).
        {
          apply leq_trans with (n := n * task_cost tsk_k);
            last by rewrite leq_mul2l; apply/orP; right. 
          apply leq_trans with (n := \sum_(0 <= i < n) task_cost tsk_k);
            last by rewrite big_const_nat iter_addn addn0 mulnC subn0.
          rewrite big_nat_cond [\sum_(0 <= i < n) task_cost _]big_nat_cond.
          apply leq_sum; intros i; rewrite andbT; move => /andP LT; des.
          by apply LTserv; rewrite INboth mem_nth // SIZE ltnS leqW.
        }

        (* Conclude that the distance between first and last is at least n + 1 periods,
           where n is the number of middle jobs. *)
        assert (DIST: job_arrival j_lst - job_arrival j_fst >= n.+1 * (task_period tsk_k)).
        {
          assert (EQnk: n.+1=(size sorted_jobs).-1); first by rewrite SIZE. 
          unfold j_fst, j_lst; rewrite EQnk telescoping_sum; last by rewrite SIZE.
          rewrite -[_ * _ tsk_k]addn0 mulnC -iter_addn -{1}[_.-1]subn0 -big_const_nat. 
          rewrite big_nat_cond [\sum_(0 <= i < _)(_-_)]big_nat_cond.
          apply leq_sum; intros i; rewrite andbT; move => /andP LT; des.
          {
            (* To simplify, call the jobs 'cur' and 'next' *)
            set cur := nth elem sorted_jobs i.
            set next := nth elem sorted_jobs i.+1.
            clear LT LTserv j_fst j_lst AFTERt1 BEFOREarr a_fst COMPok FSTok
                  LSTtask LSTin LSTserv DLi DLfst DLlst INfst BEFOREt2 FSTserv FSTtask FSTin.

            (* Show that cur arrives earlier than next *)
            assert (ARRle: job_arrival cur <= job_arrival next).
            {
              unfold cur, next; rewrite -addn1; apply prev_le_next; first by rewrite SIZE.
              by apply leq_trans with (n := i.+1); try rewrite addn1.
            }
             
            (* Show that both cur and next are in the arrival sequence *)
            assert (INnth: cur \in interfering_jobs /\
                           next \in interfering_jobs).
              rewrite 2!INboth; split.
              by apply mem_nth, (ltn_trans LT0); destruct sorted_jobs; ins.
              by apply mem_nth; destruct sorted_jobs; ins.
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
          }
        }

        (* Prove that n_k is at least the number of the middle jobs *)
        assert (NK: n_k >= n.+1).
        {
          rewrite leqNgt; apply/negP; unfold not; intro LTnk; unfold n_k in LTnk.
          rewrite ltn_divLR in LTnk; last by specialize (TASK_PARAMS tsk_k INk); des.
          apply (leq_trans LTnk) in DIST; rewrite ltn_subRL in DIST.
          rewrite -(ltn_add2r D_k) -addnA [D_i + _]addnC addnA in DIST. 
          apply leq_ltn_trans with (m := job_arrival j_i + D_i) in DIST; last first.
          {
            rewrite leq_add2r; apply (leq_trans (AFTERt1 FSTok)).
            by rewrite leq_add2l; apply NOMISS.
          }
          apply PRIOinterf in LSTserv.
          unfold D_i, D_k in DIST; rewrite -JOBtsk -{1}LSTtask in DIST.
          assert (PARAMSfst := PARAMS j_i); assert (PARAMSlst := PARAMS j_lst); des.
          by rewrite -PARAMSfst1 -PARAMSlst1 ltnNge LSTserv in DIST.
        }

        (* If n_k = num_jobs - 1, then we just need to prove that the
           extra term with min() suffices to bound the workload. *)
        set a_lst := job_arrival j_lst.
        move: NK; rewrite leq_eqVlt orbC; move => /orP NK; des;
          first by rewrite ltnS leqNgt NK in NUM.
        {
          move: NK => /eqP NK; rewrite -NK [_ + job_interference _ _ _ _ _ _ _]addnC.
          rewrite NK in DIST.
          rewrite mulSnr addnC -addnA.
          apply leq_add; first by apply BOUNDmid.
          rewrite addn_minr; rewrite leq_min; apply/andP; split;
            first by apply leq_add; apply LTserv; rewrite INboth mem_nth // SIZE.
          rewrite addnC; apply leq_add;
            first by apply LTserv; rewrite INboth mem_nth // SIZE.

          assert (LEmod: D_k - R_k <= D_i %% p_k).
          {
            rewrite -subndiv_eq_mod leq_subLR.
            fold (div_floor D_i p_k) n_k; fold p_k in DIST.
            rewrite addnBA; last by apply leq_trunc_div.
            apply leq_trans with (n := R_k + D_i - (a_lst - a_fst));
              last by apply leq_sub2l.
            rewrite subnBA; last by apply BEFOREarr.
            rewrite -(leq_add2r a_lst) subh1; last first.
            {
              apply leq_trans with (n := t2); first by apply ltnW, BEFOREt2.
              rewrite addnC addnA.
              apply leq_trans with (n := t1 + D_i);
                first by unfold t2; rewrite leq_add2l; apply NOMISS.
              by rewrite leq_add2r; apply AFTERt1.
            }
            rewrite -addnBA // subnn addn0 [D_k + _]addnC.
            apply leq_trans with (n := t1 + D_i);
              last by rewrite -addnA [D_i + _]addnC addnA leq_add2r addnC AFTERt1.
            by unfold D_i, D_k; rewrite -DLi -DLlst; apply PRIOinterf in LSTserv.
          }
          
          apply subh3; last by apply LEmod.
          rewrite -subndiv_eq_mod; apply subh3; last by apply leq_trunc_div.

          apply leq_trans with (n := \sum_(t1 <= t < a_fst + R_k) 1 + (D_k - R_k) + D_i %/ p_k * p_k).
          {
            rewrite 2!leq_add2r.
            destruct (leqP t2 (a_fst + R_k)) as [LEt2 | GTt2].
            {
              apply leq_trans with (n := job_interference job_cost rate sched j_i j_fst t1 (a_fst + R_k));
                first by apply extend_sum; rewrite ?leqnn.
              by apply leq_sum; ins; rewrite leq_b1.
            }
            {
              unfold job_interference.
              rewrite -> big_cat_nat with (n := a_fst + R_k);
                [simpl | by apply AFTERt1, FSTok | by apply ltnW].
              rewrite -[\sum_(_ <= _ < _) 1]addn0; apply leq_add;
                first by apply leq_sum; ins; apply leq_b1.
              apply leq_trans with (n := service_during rate sched j_fst (a_fst + R_k) t2);
                first by apply job_interference_le_service; ins; rewrite RATE.
              rewrite leqn0; apply/eqP.
              by apply cumulative_service_after_job_rt_zero with (job_cost0 := job_cost) (R := R_k); rewrite ?leqnn.
            }
          }

          apply leq_trans with (n := \sum_(t1 <= t < a_fst + R_k) 1 + (D_k - R_k) + (a_lst - a_fst));
            first by rewrite leq_add2l.
          apply leq_trans with (n := \sum_(t1 <= t < a_fst + R_k) 1 + \sum_(a_fst + R_k <= t < a_fst + D_k) 1 + \sum_(a_fst + D_k <= t < a_lst + D_k) 1).
          {
            by rewrite -2!addnA leq_add2l; apply leq_add;
            rewrite big_const_nat iter_addn mul1n addn0;
            rewrite ?subnDl ?subnDr leqnn.
          }
          rewrite -big_cat_nat;
            [simpl | by apply AFTERt1 | by rewrite leq_add2l; apply NOMISS].
          rewrite -big_cat_nat; simpl; last 2 first.
          {
            apply leq_trans with (n := a_fst + R_k); first by apply AFTERt1.
            by rewrite leq_add2l; apply NOMISS.
          }
          {
            rewrite leq_add2r; unfold a_fst, a_lst, j_fst, j_lst.
            rewrite -[n.+1]add0n; apply prev_le_next; rewrite ?add0n;
            by destruct (size sorted_jobs) eqn:DES; rewrite DES;
            ins; try apply ALL; rewrite /= -ltnS -SIZE ?ltnSn.
          }
          rewrite big_const_nat iter_addn mul1n addn0 leq_subLR.
          by unfold D_k, D_i; rewrite -DLi -DLlst; apply PRIOinterf in LSTserv.
        }*)
      
