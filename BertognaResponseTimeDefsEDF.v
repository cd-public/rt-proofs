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
          minn e_other ((d_tsk %% p_other) - d_other + R_other).

      
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

        assert (r: JobIn arr_seq -> nat). admit.
        assert (BEFOREr: forall j, service rate sched j (job_arrival j + r j - 1) = job_cost j - 1).
        {
          admit.
        }
        assert (ATr: forall j, service rate sched j (job_arrival j + r j) = job_cost j).
        {
          admit.
        }

        assert (COMPFIRST: forall (j j': JobIn arr_seq) tsk tsk',
                             job_task j = tsk ->
                             job_task j' = tsk' ->
                             is_interfering_task_jlfp tsk' tsk ->
                             job_arrival j + job_deadline j < job_arrival j' + job_deadline j' ->
                             job_arrival j + r j <= job_arrival j' + r j').
        {
          admit. (* True, because j interferes with j'. *)
        }
        
        
        rewrite eqn_leq; apply/andP; split; first by apply COMP.
        apply leq_trans with (n := service rate sched j (job_arrival j + r j));
          first by rewrite ATr.
        apply service_monotonic; rewrite leq_add2l.

        remember (job_arrival j + r j) as ctime.
        
        generalize dependent R.
        generalize dependent tsk.
        generalize dependent j.
        clear R tsk j.

        induction ctime as [ctime IH] using strong_ind_lt.

        assert (BEFOREok: forall j tsk R,
                            job_arrival j + r j < ctime ->
                            job_task j = tsk ->
                            (tsk, R) \in rt_bounds ->
                            service rate sched j (job_arrival j + R) == job_cost j).
        {
          intros j tsk R LT JOBtsk INbounds.
          exploit (IH (job_arrival j + r j) LT j); [by done | by apply JOBtsk | by apply INbounds |].
          intros LE; rewrite eqn_leq; apply/andP; split; first by apply COMP.
          by rewrite -ATr; apply service_monotonic; rewrite leq_add2l.
        } clear IH.

        intros j' EQc tsk' JOBtsk R INbounds; subst ctime.
        
        cut (service rate sched j' (job_arrival j' + R) == job_cost j').
        {
          intros SERV; rewrite leqNgt; apply/negP; unfold not; intro BUG.
          specialize (BEFOREr j'); destruct (r j'); first by done.
          rewrite -addn1 addnA -addnBA // subnn addn0 in BEFOREr.
          rewrite ltnS -(leq_add2l (job_arrival j')) in BUG.
          apply service_monotonic with (num_cpus0 := num_cpus) (rate0 := rate)
                                       (sched0 := sched) (j := j') in BUG.
          move: SERV => /eqP SERV; rewrite SERV BEFOREr -(leq_add2r 1) subh1 in BUG;
            last by unfold valid_realtime_job in *; specialize (PARAMS j'); des.
          rewrite -addnBA // subnn addn0 in BUG.
          by apply leq_ltn_trans with (p := job_cost j' + 1) in BUG;
            [by rewrite ltnn in BUG | by rewrite addn1].
        }

        (* First, rewrite the claim in terms of the *absolute* response-time bound (arrival + R) *)
        (*remember (job_arrival j + R) as ctime; rename Heqctime into EQc.
        assert (R = ctime - job_arrival j).
        {
          by rewrite -[R](addKn (job_arrival j)) -EQc.
        } subst R; clear EQc.
        revert tsk j JOBtsk INbounds.

        (* Now, we apply strong induction on the absolute response-time bound. *)
        induction ctime as [ctime BEFOREok] using strong_ind_lt.
        intros tsk' j' JOBtsk INbounds.
        remember (ctime - job_arrival j') as R. 
        assert (EQc: ctime = job_arrival j' + R).
        {
          rewrite HeqR addnBA; first by rewrite addnC -addnBA // subnn addn0.
          specialize (GE_COST tsk' R INbounds).
          rewrite leqNgt; apply/negP; red; intros BUG.
          apply ltnW in BUG; rewrite -subn_eq0 in BUG; move: BUG => /eqP BUG.
          rewrite HeqR BUG leqNgt in GE_COST.
          exploit (TASK_PARAMS tsk');
            [by ins; apply (INts tsk' R) | unfold is_valid_sporadic_task; intro PARAMStsk; des].
          by unfold task_cost_positive in PARAMStsk; rewrite PARAMStsk in GE_COST.
        } subst ctime; clear HeqR.
         *)
        
        (* According to the IH, all jobs with absolute response-time bound t < (job_arrival j + R)
           have correct response-time bounds.
           Now, we prove the same result for job j by contradiction.
           Assume that (job_arrival j + R) is not a response-time bound for job j. *)
        destruct (completed job_cost rate sched j' (job_arrival j' + R)) eqn:COMPLETED;
          first by move: COMPLETED => /eqP COMPLETED; rewrite COMPLETED eq_refl.
        apply negbT in COMPLETED; exfalso.

        (* Let x be the cumulative time during [job_arrival j, job_arrival j + R)
           where a job j is interfered with by tsk_k, ... *)
        set x := fun tsk_other =>
               if (tsk_other \in ts) && is_interfering_task_jlfp tsk' tsk_other then
                  task_interference job_cost job_task rate sched j'
                     tsk_other (job_arrival j') (job_arrival j' + R)
               else 0.

        (* ..., and let X be the cumulative time in the same interval where j is interfered
           with by any task. *)
        set X :=
          total_interference job_cost rate sched j' (job_arrival j') (job_arrival j' + R).
        
        (* Let's recall the interference bound under EDF scheduling. *)
        set I_edf := fun (tup: task_with_response_time) =>
          let (tsk_k, R_k) := tup in
            if is_interfering_task_jlfp tsk' tsk_k then
              interference_bound_edf task_cost task_period task_deadline tsk' R (tsk_k, R_k)
            else 0.
        
        (* Since j has not completed, recall the time when it is not
           executing is the total interference. *)
        exploit (complement_of_interf_equals_service job_cost rate sched j' (job_arrival j')
                                                     (job_arrival j' + R));
          last intro EQinterf; ins; unfold has_arrived;
          first by apply leqnn.
        rewrite {2}[_ + R]addnC -addnBA // subnn addn0 in EQinterf.
        
        (* In order to derive a contradiction, we first show that per-task
           interference x_k is no larger than the basic interference bound (based on W). *)
        assert (BASICBOUND:
                  forall tsk_k R_k,
                    (tsk_k, R_k) \in rt_bounds ->
                                     x tsk_k <= W task_cost task_period tsk_k R_k R).
        {
          intros tsk_k R_k INBOUNDSk.
          unfold x.
          destruct ((tsk_k \in ts) && is_interfering_task_jlfp tsk' tsk_k) eqn:INTERFk;
            last by done.
          move: INTERFk => /andP [INk INTERFk].
          unfold task_interference.
          apply leq_trans with (n := workload job_task rate sched tsk_k
                                     (job_arrival j') (job_arrival j' + R));
            first by apply task_interference_le_workload; ins; rewrite RATE.
          apply workload_bounded_by_W with (task_deadline0 := task_deadline) (job_cost0 := job_cost) (job_deadline0 := job_deadline); try (by ins); last 2 first;
            [ by apply GE_COST
            | by ins; apply BEFOREok with (tsk := tsk_k); admit (* FIX!!! *)
            | by ins; rewrite RATE
            | by ins; apply TASK_PARAMS
            | by ins; apply RESTR |].
          red; move => j'' /eqP JOBtsk' LEdl; unfold job_misses_no_deadline.
          assert (PARAMS' := PARAMS j''); des; rewrite PARAMS'1 JOBtsk'.
          apply completion_monotonic with (t := job_arrival j'' + (R_k)); ins;
            first by rewrite leq_add2l; apply NOMISS.
          apply BEFOREok with (tsk := tsk_k); try (by done).
          admit.
          (*apply COMPFIRST with (tsk := tsk_k) (tsk' := tsk'); try (by ins).
          apply leq_trans with (n := job_arrival j' + R); first by done.
          specialize (PARAMS j'); des; rewrite PARAMS1 JOBtsk.
          by rewrite leq_add2l; apply NOMISS.*)
        }

        assert (EDFBOUND:
                forall tsk_k R_k,
                  (tsk_k, R_k) \in rt_bounds ->
                  x tsk_k <= edf_specific_bound task_cost task_period task_deadline tsk' (tsk_k, R_k)).
        {
          unfold valid_sporadic_taskset, is_valid_sporadic_task, valid_sporadic_job in *.
          intros tsk_k R_k INBOUNDSk.
          unfold x; destruct ((tsk_k \in ts) && is_interfering_task_jlfp tsk' tsk_k) eqn:INTERFk;
            last by done.
          move: INTERFk => /andP [INk INTERFk].
          unfold edf_specific_bound; simpl.

          rename j' into j_i, tsk' into tsk_i.
          set t1 := job_arrival j_i.
          set t2 := job_arrival j_i + task_deadline tsk_i.
          set d_i := task_deadline tsk_i; set d_k := task_deadline tsk_k;
          set p_k := task_period tsk_k.

          (* TODO: CHECK IF WE CAN USE R_i instead of d_i as the problem window. *)
          apply leq_trans with (n := task_interference job_cost job_task rate sched j_i
                                                                tsk_k t1 (t1 + d_i));
            first by apply task_interference_monotonic;
              [by apply leqnn | by rewrite leq_add2l; apply NOMISS].
          
          rewrite interference_eq_interference_joblist; last by done.
          unfold task_interference_joblist.

      (* Simplify names *)
          set n_k := div_floor d_i p_k.
      
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
          admit.
        }

        assert (LEr: R < r j_i).
        {
          admit.
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

        assert (DLfst: job_deadline j_fst = task_deadline tsk_k).
        {
          by specialize (PARAMS j_fst); des; rewrite PARAMS1 FSTtask.
        }

        assert (DLi: job_deadline j_i = task_deadline tsk_i).
        {
          by specialize (PARAMS j_i); des; rewrite PARAMS1 JOBtsk.
        }

        assert (SLACKfst: job_interference job_cost rate sched j_i j_fst (job_arrival j_fst + R_k) (job_arrival j_fst + d_k) = 0).
        {
          apply/eqP; rewrite -leqn0.
          apply leq_trans with (n := service_during rate sched j_fst (job_arrival j_fst + R_k) (job_arrival j_fst + d_k));
            first by apply job_interference_le_service; ins; rewrite RATE.
          rewrite leqn0; apply/eqP.
          apply sum_service_after_job_rt_zero with (job_cost0 := job_cost) (R0 := R_k);
            try (by done); last by apply leqnn.
          apply BEFOREok with (tsk := tsk_k); try (by done).
          apply leq_ltn_trans with (n := job_arrival j_i + R);
            last by rewrite ltn_add2l.
          destruct (job_arrival j_fst + job_deadline j_fst <= job_arrival j_i + R) eqn:BLA.
          (* Don't know how to prove this *)
          admit. admit.
        }

        assert (AFTERt1: t1 <= job_arrival j_fst + R_k).
        {
          
          apply PRIOinterf in FSTserv.
          admit.
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
          destruct (ltnP d_k d_i) as [LEdi | GTdi]; last first.
          {
            rewrite -subn_eq0 in GTdi; move: GTdi => /eqP GTdi.
            rewrite GTdi add0n.
            apply leq_trans with (n := task_cost tsk_k); last by apply GE_COST.
            by apply LTserv; rewrite INboth mem_nth // SIZE.
          }
          {
            unfold job_interference; rewrite subh1; last by apply ltnW.
            rewrite -subnBA; last by apply NOMISS.
          
            destruct (leqP (job_arrival j_fst + d_k) t2) as [LEk | GTk];
            destruct (leqP t1 (job_arrival j_fst)) as [LE1 | GT1].
            {
              rewrite -> big_cat_nat with (n := job_arrival j_fst + d_k);
                [simpl | by apply (leq_trans LE1), leq_addr | by done].
              rewrite -> big_cat_nat with (n := job_arrival j_fst + R_k);
                [simpl | by apply (leq_trans LE1), leq_addr | by rewrite leq_add2l; apply NOMISS ].
              unfold job_interference in SLACKfst; rewrite SLACKfst addn0.
              apply leq_trans with (n := (\sum_(t1 <= i < job_arrival j_fst + R_k) 1) + (\sum_(job_arrival j_fst + d_k <= i < t2) 1));
                first by apply leq_add; apply leq_sum; ins; apply leq_b1.
              rewrite 2!big_const_nat 2!iter_addn 2!mul1n 2!addn0.
              rewrite addnC subh1 // addnBA; last by apply (leq_trans LE1), leq_addr.
              rewrite [_ + R_k]addnC addnA subnAC -subnBA; last by apply leq_addr.
              rewrite [_ + d_k]addnC. rewrite -[d_k + _ - _]addnBA // subnn addn0.
              rewrite subnAC -subh1; unfold t2; rewrite [_ + task_deadline tsk_i]addnC;
                last by apply leq_addl.
              by rewrite addnK subnBA; last by apply NOMISS.
            }
            {
              rewrite -> big_cat_nat with (n := job_arrival j_fst + d_k); [simpl | | by done];
                last by apply leq_trans with (n := job_arrival j_fst + R_k);
                  [by apply AFTERt1 | by rewrite leq_add2l; apply NOMISS].
              rewrite -> big_cat_nat with (n := job_arrival j_fst + R_k);
                [simpl | by apply AFTERt1 | by rewrite leq_add2l; apply NOMISS ].
              unfold job_interference in SLACKfst; rewrite SLACKfst addn0.
              apply leq_trans with (n := (\sum_(t1 <= i < job_arrival j_fst + R_k) 1) + (\sum_(job_arrival j_fst + d_k <= i < t2) 1));
                first by apply leq_add; apply leq_sum; ins; apply leq_b1.
              rewrite 2!big_const_nat 2!iter_addn 2!mul1n 2!addn0.
              rewrite addnC subh1 // addnBA; last by apply AFTERt1.
              rewrite [_ + R_k]addnC addnA subnAC -subnBA; last by apply leq_addr.
              rewrite [_ + d_k]addnC; rewrite -[d_k + _ - _]addnBA // subnn addn0.
              rewrite subnAC -subh1; unfold t2; rewrite [_ + task_deadline tsk_i]addnC;
                last by apply leq_addl.
              by rewrite addnK subnBA; last by apply NOMISS.
            }
            {              
              admit.
            }
            {
              admit.
            }            
          }
        } rewrite [nth]lock /= -lock in ALL.
    
        (* Knowing that we have at least two elements, we take first and last out of the sum *) 
        rewrite [nth]lock big_nat_recl // big_nat_recr // /= -lock.
        rewrite addnA addnC addnA.
        
        set j_lst := (nth elem sorted_jobs n.+1); fold j_fst.
                       
        (* Now we infer some facts about how first and last are ordered in the timeline *)
        assert (INfst: j_fst \in interfering_jobs).
          by unfold j_fst; rewrite INboth; apply mem_nth; destruct sorted_jobs; ins.
        move: INfst; rewrite mem_filter; move => /andP INfst; des.
        move: INfst => /andP INfst; des.

        assert (INlst: j_lst \in interfering_jobs).
          by unfold j_lst; rewrite INboth; apply mem_nth; rewrite SIZE.
        move: INlst; rewrite mem_filter; move => /andP INlst; des.
        move: INlst => /andP INlst; des.
        move: INfst INlst => /eqP INfst /eqP INlst.

        (*assert (AFTERt1': t1 <= job_arrival j_lst).
        {
          rewrite leqNgt; apply /negP; unfold not; intro LTt1.
          apply H_no_carry_in; exists j_lst; split; first by apply/eqP.
          unfold is_carry_in_job, carried_in; apply/andP; split; first by done.
          unfold completed_jobs_dont_execute, completed in *.
          apply/negP; intro COMPLETED.
          specialize (COMP j_lst t2); rewrite leqNgt in COMP.
          move: COMP => /negP COMP; apply COMP.
          unfold service; rewrite -> big_cat_nat with (n := t1);
            [simpl | by done | by apply leq_addr].
          move: COMPLETED => /eqP COMPLETED; rewrite -COMPLETED.
          apply leq_trans with (n := service rate sched j_lst t1 + 1);
            first by rewrite addn1.
          by rewrite leq_add2l lt0n.
        }*)

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

        (* Next, we upper-bound the service of the first and last jobs using their arrival times. *)
        (*assert (BOUNDend: service_during rate sched j_fst t1 t2 +
                          service_during rate sched j_lst t1 t2 <=
                          (job_arrival j_fst  + R_tsk - t1) + (t2 - job_arrival j_lst)).
        {
          apply leq_add; unfold service_during.
          {
            rewrite -[_ + _ - _]mul1n -[1*_]addn0 -iter_addn -big_const_nat.
            apply leq_trans with (n := \sum_(t1 <= t < job_arrival j_fst + R_tsk)
                                           service_at rate sched j_fst t);
              last by apply leq_sum; ins; apply service_at_le_max_rate.
            destruct (job_arrival j_fst + R_tsk < t2) eqn:LEt2; last first.
            {
              unfold t2; apply negbT in LEt2; rewrite -ltnNge in LEt2.
              rewrite -> big_cat_nat with (n := t1 + delta) (p := job_arrival j_fst + R_tsk);
                [by apply leq_addr | by apply leq_addr | by done].
            }
            {
              rewrite -> big_cat_nat with (n := job_arrival j_fst + R_tsk); [| by ins|by apply ltnW].
              rewrite -{2}[\sum_(_ <= _ < _) _]addn0 /=.
              rewrite leq_add2l leqn0; apply/eqP.
              apply (sum_service_after_job_rt_zero job_cost) with (R := R_tsk);
                try (by done); last by apply leqnn.
              by apply H_response_time_bound; first by apply/eqP.
            }
          }
          {
            rewrite -[_ - _]mul1n -[1 * _]addn0 -iter_addn -big_const_nat.
            destruct (job_arrival j_lst <= t1) eqn:LT.
            {
              apply leq_trans with (n := \sum_(job_arrival j_lst <= t < t2)
                                          service_at rate sched j_lst t);
                first by rewrite -> big_cat_nat with (m := job_arrival j_lst) (n := t1);
                  [by apply leq_addl | by ins | by apply leq_addr].
              by apply leq_sum; ins; apply service_at_le_max_rate.
            }
            {
              apply negbT in LT; rewrite -ltnNge in LT.
              rewrite -> big_cat_nat with (n := job_arrival j_lst); [|by apply ltnW| by apply ltnW].
              rewrite /= -[\sum_(_ <= _ < _) 1]add0n; apply leq_add.
              rewrite sum_service_before_arrival; [by apply leqnn | by ins | by apply leqnn].
              by apply leq_sum; ins; apply service_at_le_max_rate.
            }
          }
        }*)

        (* Let's simplify the expression of the bound *)
        (*assert (SUBST: job_arrival j_fst + R_tsk - t1 + (t2 - job_arrival j_lst) =
                       delta + R_tsk - (job_arrival j_lst - job_arrival j_fst)).
        {
          rewrite addnBA; last by apply ltnW.
          rewrite subh1 // -addnBA; last by apply leq_addr.
          rewrite addnC [job_arrival _ + _]addnC.
          unfold t2; rewrite [t1 + _]addnC -[delta + t1 - _]subnBA // subnn subn0.
          rewrite addnA -subnBA; first by ins.
          {
            unfold j_fst, j_lst; rewrite -[n.+1]add0n.
            by apply prev_le_next; [by rewrite SIZE | by rewrite SIZE add0n ltnSn].
          }
        } rewrite SUBST in BOUNDend; clear SUBST.*)

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
            clear LT LTserv j_fst j_lst AFTERt1
                  SLACKfst DLi DLfst INfst INlst INlst0 INlst1 INfst0 INfst1 BEFOREt2 FSTserv FSTtask FSTin.

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
          (* The absolute deadline of j_fst must be inside the interval, otherwise
             j_lst would be so distant that it wouldn't interfere with j_i. *)
          rewrite leqNgt; apply/negP; unfold not; intro LTnk; unfold n_k in LTnk.
          rewrite ltn_divLR in LTnk; last by specialize (TASK_PARAMS tsk_k INk); des.
          apply (leq_trans LTnk) in DIST; rewrite ltn_subRL in DIST.
          rewrite -(ltn_add2r d_k) -addnA [d_i + _]addnC addnA in DIST. 
          apply leq_ltn_trans with (m := job_arrival j_i + d_i) in DIST;
            last by rewrite leq_add2r; apply (leq_trans AFTERt1); rewrite leq_add2l; apply NOMISS.
          apply PRIOinterf in INlst1.
          unfold d_i, d_k in DIST; rewrite -JOBtsk -{1}INlst in DIST.
          assert (PARAMSfst := PARAMS j_i); assert (PARAMSlst := PARAMS j_lst); des.
          by rewrite -PARAMSfst1 -PARAMSlst1 ltnNge INlst1 in DIST.
        }

        (* If n_k = num_jobs - 1, then we just need to prove that the
           extra term with min() suffices to bound the workload. *)
        move: NK; rewrite leq_eqVlt orbC; move => /orP NK; des;
          first by rewrite ltnS leqNgt NK in NUM.
        {
          move: NK => /eqP NK; rewrite -NK. rewrite [_ + job_interference _ _ _ _ _ _ _]addnC.
          rewrite -addnA addnC; apply leq_add.
          rewrite mulSn; apply leq_add;
            first by apply LTserv; rewrite INboth mem_nth // SIZE.
          rewrite mulnC -{2}[n]subn0 -[_*_]addn0 -iter_addn -big_const_nat.
          rewrite big_nat_cond [\sum_(_ <= _ < _ | true)_]big_nat_cond.
          apply leq_sum; intros i; rewrite andbT; move => /andP [_ LE];
            first by apply LTserv; rewrite INboth mem_nth // SIZE ltnW // 2!ltnS.
          rewrite leq_min; apply/andP; split;
            first by apply LTserv; rewrite INboth mem_nth // SIZE.
          admit. (* Don't know how to prove this yet. *)
        }
      }
        
        (* In the remaining of the proof, we show that the workload bound
           W_k is less than the task interference x (contradiction!).
           For that, we require a few auxiliary lemmas: *)

        (* 1) We show that the total interference X >= R - e_k + 1.
              Otherwise, job j would have completed on time. *)
        assert (INTERF: X >= R - task_cost tsk' + 1).
        {
          unfold completed in COMPLETED.
          rewrite addn1.
          move: COMPLETED; rewrite neq_ltn; move => /orP COMPLETED; des;
            last first.
          {
            apply (leq_ltn_trans (COMP j' (job_arrival j' + R))) in COMPLETED.
            by rewrite ltnn in COMPLETED.
          }
          apply leq_trans with (n := R - service rate sched j' (job_arrival j' + R)); last first.
          {
            unfold service; rewrite service_before_arrival_eq_service_during; ins.
            rewrite EQinterf.
            rewrite subKn; first by ins.
            {
              unfold total_interference.
              rewrite -{1}[_ j']add0n big_addn addnC -addnBA // subnn addn0.
              rewrite -{2}[R]subn0 -[R-_]mul1n -[1*_]addn0 -iter_addn.
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
            by rewrite [R](FIX tsk'); first by apply leq_addr.
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
          by apply (INVARIANT tsk' j'); try (by done); apply (INts tsk' R).   
        }
        
        (* 3) Next, we prove the auxiliary lemma from the paper. *)
        assert (MINSERV: \sum_(tsk_k <- ts) x tsk_k >=
                         (R - task_cost tsk' + 1) * num_cpus ->
               \sum_(tsk_k <- ts) minn (x tsk_k) (R - task_cost tsk' + 1) >=
               (R - task_cost tsk' + 1) * num_cpus).
        {
          intro SUMLESS.
          set more_interf := fun tsk_k => x tsk_k >= R - task_cost tsk' + 1.
          rewrite [\sum_(_ <- _) minn _ _](bigID more_interf) /=.
          unfold more_interf, minn.
          rewrite [\sum_(_ <- _ | R - _ + _ <= _)_](eq_bigr (fun i => R - task_cost tsk' + 1));
            last first.
          {
            intros i COND; rewrite leqNgt in COND.
            destruct (R - task_cost tsk' + 1 > x i); ins.
          }
          rewrite [\sum_(_ <- _ | ~~_)_](eq_big (fun i => x i < R - task_cost tsk' + 1)
                                                (fun i => x i));
            [| by red; ins; rewrite ltnNge
             | by intros i COND; rewrite -ltnNge in COND; rewrite COND].

          (* Case 1 |A| = 0 *)
          destruct (~~ has (fun i => R - task_cost tsk' + 1 <= x i) ts) eqn:HASa.
          {
            rewrite [\sum_(_ <- _ | _ <= _) _]big_hasC; last by apply HASa.
            rewrite big_seq_cond; move: HASa => /hasPn HASa.
            rewrite add0n (eq_bigl (fun i => (i \in ts) && true));
              last by red; intros tsk_k; destruct (tsk_k \in ts) eqn:INk;
                [by rewrite andTb ltnNge; apply HASa | by rewrite andFb].
            by rewrite -big_seq_cond.
          } apply negbFE in HASa.
          
          set cardA := count (fun i => R - task_cost tsk' + 1 <= x i) ts.
          destruct (cardA >= num_cpus) eqn:CARD.
          {
            apply leq_trans with ((R - task_cost tsk' + 1) * cardA);
              first by rewrite leq_mul2l; apply/orP; right.
            unfold cardA; rewrite -sum1_count big_distrr /=.
            rewrite -[\sum_(_ <- _ | _) _]addn0.
            by apply leq_add; [by apply leq_sum; ins; rewrite muln1|by ins].
          } apply negbT in CARD; rewrite -ltnNge in CARD.

          assert (GEsum: \sum_(i <- ts | x i < R - task_cost tsk' + 1) x i >=
                           (R - task_cost tsk' + 1) * (num_cpus - cardA)).
          {
            set some_interference_A := fun t =>
              backlogged job_cost rate sched j' t &&
              has (fun tsk_k => (is_interfering_task_jlfp tsk' tsk_k &&
                              ((x tsk_k) >= R - task_cost tsk' + 1) &&
                              task_is_scheduled job_task sched tsk_k t)) ts.      
            set total_interference_B := fun t =>
              backlogged job_cost rate sched j' t *
              count (fun tsk_k =>
                is_interfering_task_jlfp tsk' tsk_k &&
                ((x tsk_k) < R - task_cost tsk' + 1) &&
                task_is_scheduled job_task sched tsk_k t) ts.

            apply leq_trans with ((\sum_(job_arrival j' <= t < job_arrival j' + R)
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
            apply leq_trans with (\sum_(job_arrival j' <= t < job_arrival j' + R)
                                     total_interference_B t).
            {
              rewrite big_distrl /=.
              apply leq_sum; intros t _.
              unfold some_interference_A, total_interference_B. 
              destruct (backlogged job_cost rate sched j' t) eqn:BACK;
                [rewrite andTb mul1n | by ins].
              destruct (has (fun tsk_k : sporadic_task =>
                       is_interfering_task_jlfp tsk' tsk_k &&
                       (R - task_cost tsk' + 1 <= x tsk_k) &&
                       task_is_scheduled job_task sched tsk_k t) ts) eqn:HAS;
                last by ins.
              rewrite mul1n; move: HAS => /hasP HAS.
              destruct HAS as [tsk_k INk H].
              move: H => /andP [/andP [INTERFk LEk] SCHEDk].
              
              exploit INVARIANT;
                [by apply (INts tsk' R) | by apply JOBtsk | by apply BACK | intro COUNT].

              unfold cardA.
              set interfering_tasks_at_t :=
                [seq tsk_k <- ts | is_interfering_task_jlfp tsk' tsk_k &&
                                  task_is_scheduled job_task sched tsk_k t].

              rewrite -(count_filter (fun i => true)) in COUNT.
              fold interfering_tasks_at_t in COUNT.
              rewrite count_predT in COUNT.
              apply leq_trans with (n := num_cpus -
                                      count (fun i => is_interfering_task_jlfp tsk' i &&
                                                    (x i >= R -  task_cost tsk' + 1) &&
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
                                (R - task_cost tsk' + 1 <= x i) &&
                                task_is_scheduled job_task sched i t)
                             (fun tsk_k0 : sporadic_task =>
                                is_interfering_task_jlfp tsk' tsk_k0 &&
                                (x tsk_k0 < R - task_cost tsk' + 1) &&
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
                (fun i => \sum_(job_arrival j' <= t < job_arrival j' + R)
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
                destruct (x i<R - task_cost tsk' + 1);
                  [by rewrite 2!andbT andbA | by rewrite 2!andbF].
              }
            }
          }
          
          rewrite big_const_seq iter_addn addn0; fold cardA.
          apply leq_trans with (n := (R-task_cost tsk'+1)*cardA +
                                     (R-task_cost tsk'+1)*(num_cpus-cardA));
            last by rewrite leq_add2l.
          by rewrite -mulnDr subnKC //; apply ltnW.
        }

        (* 4) Now, we prove that the Bertogna's interference bound
              is not enough to cover the sum of the "minimum" term over
              all tasks (artifact of the proof by contradiction). *)
        assert (SUM: \sum_((tsk_k, R_k) <- rt_bounds)
                     minn (x tsk_k) (R - task_cost tsk' + 1) >
                     I tsk' R). 
        {
          apply leq_trans with (n := \sum_(tsk_k <- ts) minn (x tsk_k) (R - task_cost tsk' + 1));
            last first.
          {
            rewrite (eq_bigr (fun i => minn (x (fst i)) (R - task_cost tsk' + 1)));
              last by ins; destruct i.
            apply leq_trans with (n := \sum_(tsk_k <- ts | is_interfering_task_jlfp tsk' tsk_k) minn (x tsk_k) (R - task_cost tsk' + 1)).
          {
            rewrite [\sum_(_ <- _ | is_interfering_task_jlfp _ _)_]big_mkcond eq_leq //.
            apply eq_bigr; intros i _; unfold x.
            destruct (is_interfering_task_jlfp tsk' i); last by rewrite andbF min0n.
            by rewrite andbT; destruct (i \in ts); last by rewrite min0n.
          }
            have MAP := big_map (fun x => fst x) (fun i => true) (fun i => minn (x i) (R - task_cost tsk' + 1)).
            unfold unzip1 in *; rewrite -MAP HASTASKS.
            rewrite big_mkcond /= big_seq_cond [\sum_(_ <- _ | true)_]big_seq_cond.
            apply leq_sum; intro i; rewrite andbT; intro INi.
            unfold x; rewrite INi andTb.
            by destruct (is_interfering_task_jlfp tsk' i).
          }
          apply ltn_div_trunc with (d := num_cpus); first by apply H_at_least_one_cpu.
          rewrite -(ltn_add2l (task_cost tsk')) -FIX; last by done.
          rewrite -addn1 -leq_subLR.
          rewrite -[R + 1 - _]subh1; last by apply GE_COST.
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
                              (minn (x tsk_k) (R - task_cost tsk' + 1)  >
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