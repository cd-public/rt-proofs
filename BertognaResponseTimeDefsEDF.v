Require Import Vbase TaskDefs JobDefs TaskArrivalDefs ScheduleDefs
        PlatformDefs WorkloadDefs SchedulabilityDefs PriorityDefs
        ResponseTimeDefs BertognaResponseTimeDefs divround helper
        ssreflect ssrbool eqtype ssrnat seq fintype bigop div path tuple.

Module ResponseTimeAnalysisEDF.

  Export Job SporadicTaskset ScheduleOfSporadicTask Workload Schedulability ResponseTime Priority SporadicTaskArrival ResponseTimeAnalysis.

  Section InterferenceBoundEDF.

    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> nat.
    Variable task_period: sporadic_task -> nat.
    Variable task_deadline: sporadic_task -> nat.
    
    (* Let tsk be the task to be analyzed. *)
    Variable tsk: sporadic_task.

    Let task_with_response_time := (sporadic_task * time)%type.
    
    (* Assume a known response-time bound for each interfering task ... *)
    Variable R_prev: seq task_with_response_time.

    (* ... and an interval length delta. *)
    Variable delta: time.

    Section PerTask.

      Variable tsk_R: task_with_response_time.
      Let tsk_other := fst tsk_R.
      Let R_other := snd tsk_R.

      (* By combining Bertogna's interference bound for a work-conserving
         scheduler ... *)
      Let basic_interference_bound := interference_bound task_cost task_period tsk delta tsk_R.

      (* ... with and EDF-specific interference bound, ... *)
      Definition edf_specific_bound :=
        let d_tsk := task_deadline tsk in
        let e_other := task_cost tsk_other in
        let p_other := task_period tsk_other in
        let d_other := task_deadline tsk_other in
          (div_floor d_tsk p_other) * e_other +
          minn e_other ((d_tsk %% p_other) - (d_other - R_other)).

      
      (* Bertogna and Cirinei define the following interference bound
         under EDF scheduling. *)
      Definition interference_bound_edf :=
        minn basic_interference_bound edf_specific_bound.

    End PerTask.

    Section AllTasks.

      Definition is_interfering_task_jlfp (tsk_other: sporadic_task) :=
        tsk_other != tsk.

      (* The total interference incurred by tsk is thus bounded by: *)
      Definition total_interference_bound_edf :=
        \sum_((tsk_other, R_other) <- R_prev | is_interfering_task_jlfp tsk_other)
           interference_bound_edf (tsk_other, R_other).

    End AllTasks.

    Section Proofs.

    (* Proof of edf-specific bound should go here *)
      
    End Proofs.
    
  End InterferenceBoundEDF.

  Section ResponseTimeBound.

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
    Hypothesis H_no_intra_task_parallelism:
      jobs_of_same_task_dont_execute_in_parallel job_task sched.
    Hypothesis H_rate_equals_one :
      forall j cpu, rate j cpu = 1.
    Hypothesis H_at_least_one_cpu :
      num_cpus > 0.

    (* Assume that we have a task set where all tasks have valid
       parameters and restricted deadlines. *)
    Variable ts: taskset_of sporadic_task.
    Hypothesis H_valid_task_parameters:
      valid_sporadic_taskset task_cost task_period task_deadline ts.
    Hypothesis H_restricted_deadlines:
      forall tsk, tsk \in ts -> task_deadline tsk <= task_period tsk.

    Let no_deadline_is_missed_by_tsk (tsk: sporadic_task) :=
      task_misses_no_deadline job_cost job_deadline job_task rate sched tsk.
    Let response_time_bounded_by (j: JobIn arr_seq) (R: time) :=
      completed job_cost rate sched j (job_arrival j + R).

    (* Assume a known response-time bound R is known...  *)
    Let task_with_response_time := (sporadic_task * time)%type.
    Variable rt_bounds: seq task_with_response_time.

    (* ...for any task in the task set, ...*)
    Hypothesis H_rt_bounds_contains_all_tasks:
      unzip1 rt_bounds = ts.

    (* ..., R is a fixed-point of the response-time recurrence, ... *)
    Let I (tsk: sporadic_task) (delta: time) :=
      total_interference_bound_edf task_cost task_period task_deadline tsk rt_bounds delta.
    Hypothesis H_response_time_is_fixed_point :
      forall tsk R,
        (tsk, R) \in rt_bounds ->
        R = task_cost tsk + div_floor (I tsk R) num_cpus.
    
    (* ..., R is as larger as the task cost, ... *)
    (*Hypothesis H_response_time_bounds_ge_cost:
      forall tsk_other R,
        (tsk_other, R) \in rt_bounds -> R >= task_cost tsk_other.*)
      
    (* ..., and R is no larger than the deadline. *)
    Hypothesis H_interfering_tasks_miss_no_deadlines:
      forall tsk_other R,
        (tsk_other, R) \in rt_bounds -> R <= task_deadline tsk_other.

    (* Assume that the schedule satisfies the global scheduling
       invariant, i.e., if any job of tsk is backlogged, all
       the processors must be busy with jobs of equal or higher
       priority. *)
    Hypothesis H_global_scheduling_invariant:
      forall (tsk: sporadic_task) (j: JobIn arr_seq) (t: time),
        tsk \in ts ->
        job_task j = tsk ->
        backlogged job_cost rate sched j t ->
        count
          (fun tsk_other : sporadic_task =>
             is_interfering_task_jlfp tsk tsk_other &&
               task_is_scheduled job_task sched tsk_other t) ts = num_cpus.
        
    (* Next, we define Bertogna and Cirinei's response-time bound recurrence *)  
    Variable tsk: sporadic_task.

    Variable R: time.
    Hypothesis H_tsk_R_in_rt_bounds: (tsk, R) \in rt_bounds.

    Variable j: JobIn arr_seq.
    Hypothesis H_job_of_tsk: job_task j = tsk.

    (* Now, we prove that R bounds the response time of tsk in any schedule. *)
    Theorem bertogna_cirinei_response_time_bound_edf :
      response_time_bounded_by j R.
    Proof.
        unfold response_time_bounded_by, completed, completed_jobs_dont_execute,
             valid_sporadic_job in *.
        rename H_completed_jobs_dont_execute into COMP,
               H_valid_job_parameters into PARAMS,
               H_valid_task_parameters into TASK_PARAMS,
               H_restricted_deadlines into RESTR,
               H_rt_bounds_contains_all_tasks into HASTASKS,
               H_interfering_tasks_miss_no_deadlines into NOMISS,
               H_rate_equals_one into RATE,
               H_global_scheduling_invariant into INVARIANT,
               (*H_response_time_bounds_ge_cost into GE_COST,*)
               H_response_time_is_fixed_point into FIX,
               H_tsk_R_in_rt_bounds into INbounds,
               H_job_of_tsk into JOBtsk.

        (* Let's prove some basic facts about the tasks. *)
        assert (INts: forall tsk R, (tsk, R) \in rt_bounds -> tsk \in ts).
        {
          by intros tsk0 R0 IN0; rewrite -HASTASKS; apply/mapP; exists (tsk0, R0).
        }

        assert (GE_COST: forall tsk R, (tsk, R) \in rt_bounds -> task_cost tsk <= R).
        {
          by intros tsk0 R0 IN0; rewrite [R0](FIX tsk0); first apply leq_addr.
        }
        
        (* First, rewrite the claim in terms of the *absolute* response-time bound (arrival + R) *)
        remember (job_arrival j + R) as ctime.
        
        generalize dependent R.
        generalize dependent tsk.
        generalize dependent j.
        clear R tsk j.

        (* Now, we apply strong induction on the absolute response-time bound. *)
        induction ctime as [ctime IH] using strong_ind_lt.

        intros j' tsk' JOBtsk R' INbounds EQc; subst ctime.
        
        assert (BEFOREok: forall (j0: JobIn arr_seq) tsk R0,
                            job_task j0 = tsk ->
                            (tsk, R0) \in rt_bounds ->
                            job_arrival j0 + R0 < job_arrival j' + R' ->
                            service rate sched j0 (job_arrival j0 + R0) == job_cost j0).
        {
          by ins; apply IH with (tsk := tsk) (R := R0).
        } clear IH.
        
        (* According to the IH, all jobs with absolute response-time bound t < (job_arrival j + R)
           have correct response-time bounds.
           Now, we prove the same result for job j by contradiction.
           Assume that (job_arrival j + R) is not a response-time bound for job j. *)
        destruct (completed job_cost rate sched j' (job_arrival j' + R')) eqn:COMPLETED;
          first by move: COMPLETED => /eqP COMPLETED; rewrite COMPLETED eq_refl.
        apply negbT in COMPLETED; exfalso.

        (* Let x be the cumulative time during [job_arrival j, job_arrival j + R)
           where a job j is interfered with by tsk_k, ... *)
        set x := fun tsk_other =>
               if (tsk_other \in ts) && is_interfering_task_jlfp tsk' tsk_other then
                  task_interference job_cost job_task rate sched j'
                     tsk_other (job_arrival j') (job_arrival j' + R')
               else 0.

        (* ..., and let X be the cumulative time in the same interval where j is interfered
           with by any task. *)
        set X :=
          total_interference job_cost rate sched j' (job_arrival j') (job_arrival j' + R').
        
        (* Let's recall the interference bound under EDF scheduling. *)
        set I_edf := fun (tup: task_with_response_time) =>
          let (tsk_k, R_k) := tup in
            if is_interfering_task_jlfp tsk' tsk_k then
              interference_bound_edf task_cost task_period task_deadline tsk' R' (tsk_k, R_k)
            else 0.
        
        (* Since j has not completed, recall the time when it is not
           executing is the total interference. *)
        exploit (complement_of_interf_equals_service job_cost rate sched j' (job_arrival j')
                                                     (job_arrival j' + R'));
          last intro EQinterf; ins; unfold has_arrived;
          first by apply leqnn.
        rewrite {2}[_ + R']addnC -addnBA // subnn addn0 in EQinterf.
        
        (* In order to derive a contradiction, we first show that per-task
           interference x_k is no larger than the basic interference bound (based on W). *)
        assert (BASICBOUND:
                  forall tsk_k R_k,
                    (tsk_k, R_k) \in rt_bounds ->
                                     x tsk_k <= W task_cost task_period tsk_k R_k R').
        {
          intros tsk_k R_k INBOUNDSk.
          unfold x.
          destruct ((tsk_k \in ts) && is_interfering_task_jlfp tsk' tsk_k) eqn:INTERFk;
            last by done.
          move: INTERFk => /andP [INk INTERFk].
          unfold task_interference.
          apply leq_trans with (n := workload job_task rate sched tsk_k
                                     (job_arrival j') (job_arrival j' + R'));
            first by apply task_interference_le_workload; ins; rewrite RATE.
          apply workload_bounded_by_W with (task_deadline0 := task_deadline) (job_cost0 := job_cost) (job_deadline0 := job_deadline); try (by ins); last 2 first;
            [ by apply GE_COST
            | by ins; apply BEFOREok with (tsk := tsk_k); ins; rewrite RATE
            | by ins; rewrite RATE
            | by ins; apply TASK_PARAMS
            | by ins; apply RESTR |].
          red; move => j'' /eqP JOBtsk' LEdl; unfold job_misses_no_deadline.
          assert (PARAMS' := PARAMS j''); des; rewrite PARAMS'1 JOBtsk'.
          apply completion_monotonic with (t := job_arrival j'' + (R_k)); ins;
            first by rewrite leq_add2l; apply NOMISS.
          apply BEFOREok with (tsk := tsk_k); ins.
          apply leq_ltn_trans with (n := job_arrival j'' + job_deadline j''); last by done.
          by specialize (PARAMS j''); des; rewrite leq_add2l PARAMS1 JOBtsk'; apply NOMISS.
        }

        assert (EDFBOUND:
                forall tsk_k R_k,
                  (tsk_k, R_k) \in rt_bounds ->
                  x tsk_k <= edf_specific_bound task_cost task_period task_deadline tsk' (tsk_k, R_k)).
        {
          unfold valid_sporadic_taskset, is_valid_sporadic_task, valid_sporadic_job in *.
          intros tsk_k R_k INBOUNDSk.
          rename R' into R_i.
          unfold x; destruct ((tsk_k \in ts) && is_interfering_task_jlfp tsk' tsk_k) eqn:INTERFk;
            last by done.
          move: INTERFk => /andP [INk INTERFk].
          unfold edf_specific_bound; simpl.

          rename j' into j_i, tsk' into tsk_i.
          set t1 := job_arrival j_i.
          set t2 := job_arrival j_i + R_i.
          set D_i := task_deadline tsk_i; set D_k := task_deadline tsk_k;
          set p_k := task_period tsk_k.

          rewrite interference_eq_interference_joblist; last by done.
          unfold task_interference_joblist.

      (* Simplify names *)
          set n_k := div_floor D_i p_k.
      
        (* Identify the subset of jobs that actually cause interference *)
        set interfering_jobs :=
          filter (fun (x: JobIn arr_seq) =>
                    (job_task x == tsk_k) && (job_interference job_cost rate sched j_i x t1 t2 != 0))
                      (jobs_scheduled_between sched t1 t2).
    
        (* Remove the elements that we don't care about from the sum *)
        assert (SIMPL:
          \sum_(j <- jobs_scheduled_between sched t1 t2 | job_task j == tsk_k)
             job_interference job_cost rate sched j_i j t1 t2 = 
          \sum_(j <- interfering_jobs) job_interference job_cost rate sched j_i j t1 t2).
        {
          unfold interfering_jobs; rewrite big_filter.
          rewrite big_mkcond; rewrite [\sum_(_ <- _ | _) _]big_mkcond /=.
          apply eq_bigr; intros i _; clear -i.
          destruct (job_task i == tsk_k); rewrite ?andTb ?andFb; last by done.
          destruct (job_interference job_cost rate sched j_i i t1 t2 != 0) eqn:DIFF; first by done.
          by apply negbT in DIFF; rewrite negbK in DIFF; apply/eqP.
        } rewrite SIMPL; clear SIMPL.

        (* Remember that for any job of tsk, service <= task_cost tsk *)
        assert (LTserv: forall j (INi: j \in interfering_jobs),
                          job_interference job_cost rate sched j_i j t1 t2 <= task_cost tsk_k).
        {
          intros j; rewrite mem_filter; move => /andP [/andP [/eqP JOBj _] _]; rewrite -JOBj.
          specialize (PARAMS j); des.
          apply leq_trans with (n := job_cost j); last by ins.
          apply leq_trans with (n := service_during rate sched j t1 t2);
            first by apply job_interference_le_service; ins; rewrite RATE.
          by apply service_interval_le_cost.
        }

        (* Order the sequence of interfering jobs by arrival time, so that
           we can identify the first and last jobs. *)
        set order := fun (x y: JobIn arr_seq) => job_arrival x <= job_arrival y.
        set sorted_jobs := (sort order interfering_jobs).
        assert (SORT: sorted order sorted_jobs);
          first by apply sort_sorted; unfold total, order; ins; apply leq_total.
        rewrite (eq_big_perm sorted_jobs) /=; last by rewrite -(perm_sort order).
   
        (* Remember that both sequences have the same set of elements *)
        assert (INboth: forall x, (x \in interfering_jobs) = (x \in sorted_jobs)).
          by apply perm_eq_mem; rewrite -(perm_sort order).

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
            admit. (* Use INVARIANT -- needs some fix for EDF *)
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
          unfold service_during.
          by rewrite -> sum_service_after_job_rt_zero with (job_cost0 := job_cost) (R := R_k);
            try (by done); apply ltnW.
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
            by rewrite -> sum_service_after_job_rt_zero with (job_cost0 := job_cost) (R := R_k);
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
                rewrite -> sum_service_after_job_rt_zero with (job_cost0 := job_cost) (R := R_k);
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
            rewrite -> sum_service_after_job_rt_zero with (job_cost0 := job_cost) (R := R_k);
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
          by unfold service_during; rewrite sum_service_before_arrival.
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
            by unfold service_during; rewrite sum_service_before_arrival.
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
              unfold service_during.
              by rewrite -> sum_service_after_job_rt_zero with (job_cost0 := job_cost) (R := R_k); rewrite ?leqnn.
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
        }
      }
          
        (* In the remaining of the proof, we show that the workload bound
           W_k is less than the task interference x (contradiction!).
           For that, we require a few auxiliary lemmas: *)

        (* 1) We show that the total interference X >= R - e_k + 1.
              Otherwise, job j would have completed on time. *)
        assert (INTERF: X >= R' - task_cost tsk' + 1).
        {
          unfold completed in COMPLETED.
          rewrite addn1.
          move: COMPLETED; rewrite neq_ltn; move => /orP COMPLETED; des;
            last first.
          {
            apply (leq_ltn_trans (COMP j' (job_arrival j' + R'))) in COMPLETED.
            by rewrite ltnn in COMPLETED.
          }
          apply leq_trans with (n := R' - service rate sched j' (job_arrival j' + R')); last first.
          {
            unfold service; rewrite service_before_arrival_eq_service_during; ins.
            rewrite EQinterf.
            rewrite subKn; first by ins.
            {
              unfold total_interference.
              rewrite -{1}[_ j']add0n big_addn addnC -addnBA // subnn addn0.
              rewrite -{2}[R']subn0 -[R'-_]mul1n -[1*_]addn0 -iter_addn.
              by rewrite -big_const_nat leq_sum //; ins; apply leq_b1.
            }
          }
          {
            apply ltn_sub2l; last first.
            {
              apply leq_trans with (n := job_cost j'); first by ins.
              by rewrite -JOBtsk; specialize (PARAMS j'); des; apply PARAMS0.
            }
            apply leq_trans with (n := job_cost j'); first by ins.
            apply leq_trans with (n := task_cost tsk');
              first by rewrite -JOBtsk; specialize (PARAMS j'); des; apply PARAMS0.
            by rewrite [R'](FIX tsk'); first by apply leq_addr.
          }
        }

        (* 2) Then, we prove that the sum of the interference of each
           task is equal to the total interference multiplied by the
           number of processors. This holds because interference only
           occurs when all processors are busy with some task. *)
        assert(ALLBUSY: \sum_(tsk_k <- ts) x tsk_k = X * num_cpus).
        {
          unfold x, X, total_interference, task_interference.
          rewrite -big_mkcond -exchange_big big_distrl /=.
          apply eq_big_nat; move => t LTt.
          destruct (backlogged job_cost rate sched j' t) eqn:BACK;
            last by rewrite (eq_bigr (fun i => 0));
              [by rewrite big_const_seq iter_addn mul0n addn0 mul0n|by ins].
          rewrite big_mkcond mul1n /=.
          rewrite (eq_bigr (fun i =>
                              (if (i \in ts) && is_interfering_task_jlfp tsk' i &&
                                             task_is_scheduled job_task sched i t then 1 else 0))); last first.
          {
            ins; destruct ((i \in ts) && is_interfering_task_jlfp tsk' i) eqn:IN;
              [by rewrite andTb | by rewrite andFb].
          }
          rewrite (eq_bigr (fun i => if (i \in ts) && true then (if is_interfering_task_jlfp tsk' i && task_is_scheduled job_task sched i t then 1 else 0) else 0));
            last by ins; destruct (i \in ts) eqn:IN; rewrite ?andTb ?andFb.
          rewrite -big_mkcond -big_seq_cond -big_mkcond sum1_count.
          by apply (INVARIANT tsk' j'); try (by done); apply (INts tsk' R').   
        }
        
        (* 3) Next, we prove the auxiliary lemma from the paper. *)
        assert (MINSERV: \sum_(tsk_k <- ts) x tsk_k >=
                         (R' - task_cost tsk' + 1) * num_cpus ->
               \sum_(tsk_k <- ts) minn (x tsk_k) (R' - task_cost tsk' + 1) >=
               (R' - task_cost tsk' + 1) * num_cpus).
        {
          intro SUMLESS.
          set more_interf := fun tsk_k => x tsk_k >= R' - task_cost tsk' + 1.
          rewrite [\sum_(_ <- _) minn _ _](bigID more_interf) /=.
          unfold more_interf, minn.
          rewrite [\sum_(_ <- _ | R' - _ + _ <= _)_](eq_bigr (fun i => R' - task_cost tsk' + 1));
            last first.
          {
            intros i COND; rewrite leqNgt in COND.
            destruct (R' - task_cost tsk' + 1 > x i); ins.
          }
          rewrite [\sum_(_ <- _ | ~~_)_](eq_big (fun i => x i < R' - task_cost tsk' + 1)
                                                (fun i => x i));
            [| by red; ins; rewrite ltnNge
             | by intros i COND; rewrite -ltnNge in COND; rewrite COND].

          (* Case 1 |A| = 0 *)
          destruct (~~ has (fun i => R' - task_cost tsk' + 1 <= x i) ts) eqn:HASa.
          {
            rewrite [\sum_(_ <- _ | _ <= _) _]big_hasC; last by apply HASa.
            rewrite big_seq_cond; move: HASa => /hasPn HASa.
            rewrite add0n (eq_bigl (fun i => (i \in ts) && true));
              last by red; intros tsk_k; destruct (tsk_k \in ts) eqn:INk;
                [by rewrite andTb ltnNge; apply HASa | by rewrite andFb].
            by rewrite -big_seq_cond.
          } apply negbFE in HASa.
          
          set cardA := count (fun i => R' - task_cost tsk' + 1 <= x i) ts.
          destruct (cardA >= num_cpus) eqn:CARD.
          {
            apply leq_trans with ((R' - task_cost tsk' + 1) * cardA);
              first by rewrite leq_mul2l; apply/orP; right.
            unfold cardA; rewrite -sum1_count big_distrr /=.
            rewrite -[\sum_(_ <- _ | _) _]addn0.
            by apply leq_add; [by apply leq_sum; ins; rewrite muln1|by ins].
          } apply negbT in CARD; rewrite -ltnNge in CARD.

          assert (GEsum: \sum_(i <- ts | x i < R' - task_cost tsk' + 1) x i >=
                           (R' - task_cost tsk' + 1) * (num_cpus - cardA)).
          {
            set some_interference_A := fun t =>
              backlogged job_cost rate sched j' t &&
              has (fun tsk_k => (is_interfering_task_jlfp tsk' tsk_k &&
                              ((x tsk_k) >= R' - task_cost tsk' + 1) &&
                              task_is_scheduled job_task sched tsk_k t)) ts.      
            set total_interference_B := fun t =>
              backlogged job_cost rate sched j' t *
              count (fun tsk_k =>
                is_interfering_task_jlfp tsk' tsk_k &&
                ((x tsk_k) < R' - task_cost tsk' + 1) &&
                task_is_scheduled job_task sched tsk_k t) ts.

            apply leq_trans with ((\sum_(job_arrival j' <= t < job_arrival j' + R')
                                      some_interference_A t) * (num_cpus - cardA)).
            {
              rewrite leq_mul2r; apply/orP; right.
              move: HASa => /hasP HASa; destruct HASa as [tsk_a INa LEa].
              apply leq_trans with (n := x tsk_a); first by apply LEa.
              unfold x, task_interference, some_interference_A.
              destruct ((tsk_a \in ts) && is_interfering_task_jlfp tsk' tsk_a) eqn:INTERFa;
                last by ins.
              move: INTERFa => /andP INTERFa; des.
              apply leq_sum; ins.
              destruct (backlogged job_cost rate sched j' i);
                [rewrite 2!andTb | by ins].
              destruct (task_is_scheduled job_task sched tsk_a i) eqn:SCHEDa;
                [apply eq_leq; symmetry | by ins].
              apply/eqP; rewrite eqb1.
              apply/hasP; exists tsk_a; first by ins.
              apply/andP; split; last by ins.
              by apply/andP; split; ins.
            }
            apply leq_trans with (\sum_(job_arrival j' <= t < job_arrival j' + R')
                                     total_interference_B t).
            {
              rewrite big_distrl /=.
              apply leq_sum; intros t _.
              unfold some_interference_A, total_interference_B. 
              destruct (backlogged job_cost rate sched j' t) eqn:BACK;
                [rewrite andTb mul1n | by ins].
              destruct (has (fun tsk_k : sporadic_task =>
                       is_interfering_task_jlfp tsk' tsk_k &&
                       (R' - task_cost tsk' + 1 <= x tsk_k) &&
                       task_is_scheduled job_task sched tsk_k t) ts) eqn:HAS;
                last by ins.
              rewrite mul1n; move: HAS => /hasP HAS.
              destruct HAS as [tsk_k INk H].
              move: H => /andP [/andP [INTERFk LEk] SCHEDk].
              
              exploit INVARIANT;
                [by apply (INts tsk' R') | by apply JOBtsk | by apply BACK | intro COUNT].

              unfold cardA.
              set interfering_tasks_at_t :=
                [seq tsk_k <- ts | is_interfering_task_jlfp tsk' tsk_k &&
                                  task_is_scheduled job_task sched tsk_k t].

              rewrite -(count_filter (fun i => true)) in COUNT.
              fold interfering_tasks_at_t in COUNT.
              rewrite count_predT in COUNT.
              apply leq_trans with (n := num_cpus -
                                      count (fun i => is_interfering_task_jlfp tsk' i &&
                                                    (x i >= R' -  task_cost tsk' + 1) &&
                                                    task_is_scheduled job_task sched i t) ts).
              {
                apply leq_sub2l.
                rewrite -2!sum1_count big_mkcond /=.
                rewrite [\sum_(_ <- _ | _ <= _)_]big_mkcond /=.
                apply leq_sum; intros i _.
                unfold x; destruct (is_interfering_task_jlfp tsk' i);
                  [rewrite andTb | by rewrite 2!andFb].
                destruct (task_is_scheduled job_task sched i t);
                  [by rewrite andbT | by rewrite andbF].
              }

              rewrite leq_subLR.
              rewrite -count_predUI.
              apply leq_trans with (n :=
                count (predU (fun i : sporadic_task =>
                                is_interfering_task_jlfp tsk' i &&
                                (R' - task_cost tsk' + 1 <= x i) &&
                                task_is_scheduled job_task sched i t)
                             (fun tsk_k0 : sporadic_task =>
                                is_interfering_task_jlfp tsk' tsk_k0 &&
                                (x tsk_k0 < R' - task_cost tsk' + 1) &&
                                task_is_scheduled job_task sched tsk_k0 t))
                      ts); last by apply leq_addr.
              apply leq_trans with (n := size interfering_tasks_at_t);
                first by rewrite COUNT.
              unfold interfering_tasks_at_t.
              rewrite -count_predT count_filter.
              rewrite leq_eqVlt; apply/orP; left; apply/eqP.
              apply eq_count; red; simpl.
              intros i.
              destruct (is_interfering_task_jlfp tsk' i),
                       (task_is_scheduled job_task sched i t);
                rewrite 3?andTb ?andFb ?andbF ?andbT /=; try ins.
              by rewrite leqNgt orNb. 
            }
            {
              unfold x at 2, task_interference.
              rewrite [\sum_(i <- ts | _) _](eq_bigr
                (fun i => \sum_(job_arrival j' <= t < job_arrival j' + R')
                             (i \in ts) && is_interfering_task_jlfp tsk' i &&
                             backlogged job_cost rate sched j' t &&
                             task_is_scheduled job_task sched i t));
                last first.
              {
                ins; destruct ((i \in ts) && is_interfering_task_jlfp tsk' i) eqn:INTERi;
                  first by move: INTERi => /andP [_ INTERi]; apply eq_bigr; ins; rewrite INTERi andTb.
                by rewrite (eq_bigr (fun i => 0));
                  [by rewrite big_const_nat iter_addn mul0n addn0 | by ins].
              }
              {
                rewrite exchange_big /=; apply leq_sum; intros t _.
                unfold total_interference_B.
                destruct (backlogged job_cost rate sched j' t); last by ins.
                rewrite mul1n -sum1_count.
                rewrite big_seq_cond big_mkcond [\sum_(i <- ts | _ < _) _]big_mkcond.
                apply leq_sum; ins.
                destruct (x i<R' - task_cost tsk' + 1);
                  [by rewrite 2!andbT andbA | by rewrite 2!andbF].
              }
            }
          }

          rewrite big_const_seq iter_addn addn0; fold cardA.
          apply leq_trans with (n := (R'-task_cost tsk'+1)*cardA +
                                     (R'-task_cost tsk'+1)*(num_cpus-cardA));
            last by rewrite leq_add2l.
          by rewrite -mulnDr subnKC //; apply ltnW.
        }

        (* 4) Now, we prove that the Bertogna's interference bound
              is not enough to cover the sum of the "minimum" term over
              all tasks (artifact of the proof by contradiction). *)
        assert (SUM: \sum_((tsk_k, R_k) <- rt_bounds)
                     minn (x tsk_k) (R' - task_cost tsk' + 1) >
                     I tsk' R'). 
        {
          apply leq_trans with (n := \sum_(tsk_k <- ts) minn (x tsk_k) (R' - task_cost tsk' + 1));
            last first.
          {
            rewrite (eq_bigr (fun i => minn (x (fst i)) (R' - task_cost tsk' + 1)));
              last by ins; destruct i.
            apply leq_trans with (n := \sum_(tsk_k <- ts | is_interfering_task_jlfp tsk' tsk_k) minn (x tsk_k) (R' - task_cost tsk' + 1)).
          {
            rewrite [\sum_(_ <- _ | is_interfering_task_jlfp _ _)_]big_mkcond eq_leq //.
            apply eq_bigr; intros i _; unfold x.
            destruct (is_interfering_task_jlfp tsk' i); last by rewrite andbF min0n.
            by rewrite andbT; destruct (i \in ts); last by rewrite min0n.
          }
            have MAP := big_map (fun x => fst x) (fun i => true) (fun i => minn (x i) (R' - task_cost tsk' + 1)).
            unfold unzip1 in *; rewrite -MAP HASTASKS.
            rewrite big_mkcond /= big_seq_cond [\sum_(_ <- _ | true)_]big_seq_cond.
            apply leq_sum; intro i; rewrite andbT; intro INi.
            unfold x; rewrite INi andTb.
            by destruct (is_interfering_task_jlfp tsk' i).
          }
          apply ltn_div_trunc with (d := num_cpus); first by apply H_at_least_one_cpu.
          rewrite -(ltn_add2l (task_cost tsk')) -FIX; last by done.
          rewrite -addn1 -leq_subLR.
          rewrite -[R' + 1 - _]subh1; last by apply GE_COST.
          rewrite leq_divRL; last by apply H_at_least_one_cpu.
          apply MINSERV.
          apply leq_trans with (n := X * num_cpus); last by rewrite ALLBUSY.
          by rewrite leq_mul2r; apply/orP; right; apply INTERF.
        }
      
        (* 5) This implies that there exists a tuple (tsk_k, R_k) such that
              min (x_k, R - e_i + 1) > min (W_k, R - e_i + 1). *)
        assert (EX:
            has (fun tup : task_with_response_time => let (tsk_k, R_k) := tup in
                           (tsk_k \in ts) && is_interfering_task_jlfp tsk' tsk_k &&
                              (minn (x tsk_k) (R' - task_cost tsk' + 1)  >
                              I_edf (tsk_k, R_k)))
                 rt_bounds).
        {
          unfold I_edf; apply/negP; unfold not; intro NOTHAS.
          move: NOTHAS => /negP /hasPn ALL.
          rewrite -[_ < _]negbK in SUM.
          move: SUM => /negP SUM; apply SUM; rewrite -leqNgt.
          unfold I, total_interference_bound_edf.
          rewrite [\sum_(i <- _ | let '(tsk_other, _) := i in _)_]big_mkcond.
          rewrite big_seq_cond [\sum_(i <- _ | true) _]big_seq_cond.
          apply leq_sum; move => tsk_k /andP [INBOUNDSk _]; destruct tsk_k as [tsk_k R_k].
          assert (INtsk: tsk_k \in ts). by apply (INts tsk_k R_k).
          specialize (ALL (tsk_k, R_k) INBOUNDSk).
          unfold interference_bound_edf.
          destruct (is_interfering_task_jlfp tsk' tsk_k) eqn:INTERFk;
            last by unfold x; rewrite INTERFk andbF min0n.
          rewrite leq_min; apply/andP; split.
          {
            unfold interference_bound; rewrite leq_min; apply/andP; split;
              last by rewrite geq_minr.
            apply leq_trans with (n := x tsk_k); first by rewrite geq_minl.
            by apply BASICBOUND.
          }
          {
            apply leq_trans with (n := x tsk_k); first by rewrite geq_minl.
            by apply EDFBOUND.
          }
        }

        (* For this particular task, we show that x_k > W_k.
           This contradicts the previous claim. *)
        move: EX => /hasP EX; destruct EX as [tup_k HPk LTmin].
        destruct tup_k as [tsk_k R_k]; simpl in LTmin.
        move: LTmin => /andP [INTERFk LTmin]; move: (INTERFk) => /andP [INk INTERFk'].
        rewrite INTERFk' in LTmin.
        unfold interference_bound_edf, interference_bound in LTmin.
        rewrite minnAC in LTmin; apply min_lt_same in LTmin.
        unfold minn in LTmin; clear -LTmin EDFBOUND BASICBOUND JOBtsk HPk; desf.
        {
          specialize (BASICBOUND tsk_k R_k HPk).
          by apply (leq_ltn_trans BASICBOUND) in LTmin; rewrite ltnn in LTmin. 
        }
        {
          specialize (EDFBOUND tsk_k R_k HPk).
          by apply (leq_ltn_trans EDFBOUND) in LTmin; rewrite ltnn in LTmin.
        }
    Qed.

  End ResponseTimeBound.

End ResponseTimeAnalysisEDF.