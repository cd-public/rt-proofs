Require Import Vbase TaskDefs JobDefs TaskArrivalDefs ScheduleDefs
               PlatformDefs helper
               ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Module ResponseTime.

  Import Schedule SporadicTaskset SporadicTaskArrival.
                                    
  Section ResponseTimeBound.
    
    Context {Job: eqType}.
    Context {arr_seq: arrival_sequence Job}.
    Variable job_cost: Job -> nat.
    Variable job_task: Job -> sporadic_task.

    (* Given a task ...*)
    Variable tsk: sporadic_task.

    (* ... and a particular schedule, ...*)
    Context {num_cpus : nat}.
    Variable rate: Job -> processor num_cpus -> nat.
    Variable sched: schedule num_cpus arr_seq.

    (* ... R is a response-time bound of tsk in this schedule ... *)
    Variable R: time.

    Definition job_has_completed_by :=
      completed job_cost rate sched.

    (* ... iff any job j of tsk in this arrival sequence has
       completed by (job_arrival j + R). *)
    Definition is_response_time_bound_of_task :=
      forall (j: JobIn arr_seq),
        job_task j = tsk ->
        job_has_completed_by j (job_arrival j + R).
        
  End ResponseTimeBound.

  Section BasicLemmas.

    Context {Job: eqType}.
    Variable job_cost: Job -> nat.
    Variable job_task: Job -> sporadic_task.

    Context {arr_seq: arrival_sequence Job}.

    (* Assume a task ...*)
    Variable tsk: sporadic_task.
    
    (*...any valid schedule,...*)
    Context {num_cpus : nat}.
    Variable sched: schedule num_cpus arr_seq.
    Variable rate: Job -> processor num_cpus -> nat.

    Hypothesis H_completed_jobs_dont_execute:
      completed_jobs_dont_execute job_cost rate sched.

    (* ...and that R is a response-time bound of tsk in this schedule. *)
    Variable R: time.
    Hypothesis response_time_bound:
      is_response_time_bound_of_task job_cost job_task tsk rate sched R.

    Variable j: JobIn arr_seq.
    Hypothesis H_job_of_task: job_task j = tsk.
    
    Lemma service_at_after_rt_zero :
      forall t',
        t' >= job_arrival j + R ->
        service_at rate sched j t' = 0.
    Proof.
      rename response_time_bound into RT,
             H_completed_jobs_dont_execute into EXEC; ins.
      unfold is_response_time_bound_of_task, completed,
             completed_jobs_dont_execute in *.
      specialize (RT j H_job_of_task).
      apply/eqP; rewrite -leqn0.
      rewrite <- leq_add2l with (p := job_cost j).
      move: RT => /eqP RT; rewrite -{1}RT addn0.
      apply leq_trans with (n := service rate sched j t'.+1);
        last by apply EXEC.
      unfold service; rewrite -> big_cat_nat with
                                 (p := t'.+1) (n := job_arrival j + R);
          [rewrite leq_add2l /= | by ins | by apply ltnW].
        by rewrite big_nat_recr // /=; apply leq_addl.
    Qed.

    Lemma sum_service_after_rt_zero :
      forall t' t'',
        t' >= job_arrival j + R ->
        \sum_(t' <= t < t'') service_at rate sched j t = 0.
    Proof.
      ins; apply/eqP; rewrite -leqn0.
      rewrite big_nat_cond; rewrite -> eq_bigr with (F2 := fun i => 0);
        first by rewrite big_const_seq iter_addn mul0n addn0 leqnn.
      intro i; rewrite andbT; move => /andP [LE _].
      by rewrite service_at_after_rt_zero;
        [by ins | by apply leq_trans with (n := t')].
    Qed.

    Section CostAsLowerBound.

      Hypothesis H_jobs_must_arrive_to_execute:
        jobs_must_arrive_to_execute sched.
      Hypothesis H_no_parallelism:
        jobs_dont_execute_in_parallel sched.
      Hypothesis H_rate_at_most_one :
        forall j cpu, rate j cpu <= 1.
    
      Lemma response_time_ge_cost : R >= job_cost j.
      Proof.
        rename response_time_bound into BOUND.
        unfold is_response_time_bound_of_task, job_has_completed_by, completed,
               jobs_must_arrive_to_execute in *.
      
        specialize (BOUND j H_job_of_task).
        move: BOUND => /eqP BOUND; rewrite -BOUND.
        apply leq_trans with (n := service_during rate sched j
                                  (job_arrival j) (job_arrival j + R)).
        unfold service; rewrite -> big_cat_nat with (n := job_arrival j);
          [by rewrite sum_service_before_arrival // leqnn | by ins | by apply leq_addr].
        unfold service_during.
        apply leq_trans with (n := \sum_(job_arrival j <= t < job_arrival j + R) 1);
          last by rewrite big_const_nat iter_addn mul1n addn0 addnC -addnBA // subnn addn0 leqnn.
        by apply leq_sum; ins; by apply service_at_le_max_rate.
      Qed.
      
    End CostAsLowerBound.

  End BasicLemmas.

  Section LowerBoundOfResponseTimeBound.

    Context {Job: eqType}.
    Variable job_cost: Job -> nat.
    Variable job_task: Job -> sporadic_task.
    Context {arr_seq: arrival_sequence Job}.
    
    (* Assume a task with at least one job that arrives in this set. *)
    Variable tsk: sporadic_task.
    Hypothesis job_of_tsk_exists:
      exists j: JobIn arr_seq, job_task j = tsk.

    (* And assume any valid schedule...*)
    Context {num_cpus : nat}.
    Variable sched: schedule num_cpus arr_seq.
    Variable rate: Job -> processor num_cpus -> nat.

    (*... that satisfies the following properties: *)
    Hypothesis H_jobs_must_arrive_to_execute:
      jobs_must_arrive_to_execute sched.
    Hypothesis H_completed_jobs_dont_execute:
      completed_jobs_dont_execute job_cost rate sched.
    Hypothesis H_no_parallelism:
      jobs_dont_execute_in_parallel sched.
    Hypothesis H_rate_at_most_one:
      forall j cpu, rate j cpu <= 1.

    (* ..., and assume that, for any job cost function, R is a
            response-time bound of tsk in this schedule. *)
    Variable R: time.
    Hypothesis response_time_bound:
      forall job_cost,
        is_response_time_bound_of_task job_cost job_task tsk rate sched R.

    (* Then, R cannot be less than the cost of tsk. *)
    Lemma response_time_ub_ge_task_cost:
      R >= task_cost tsk.
    Proof.
      unfold valid_sporadic_task, job_has_completed_by, completed in *.
      rename job_of_tsk_exists into EX; des.
      set new_cost := fun (j': Job) => task_cost (job_task j').
      apply leq_trans with (n := new_cost j);
        first by unfold new_cost; rewrite EX.
      by exploit (response_time_ge_cost new_cost job_task tsk sched rate R);
        by ins; apply EX.
    Qed.

  End LowerBoundOfResponseTimeBound.
    
End ResponseTime.