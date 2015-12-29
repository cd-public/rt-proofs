Require Import Vbase task job task_arrival schedule util_lemmas
               ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Module ResponseTime.

  Import Schedule SporadicTaskset SporadicTaskArrival.
                                    
  Section ResponseTimeBound.

    Context {sporadic_task: eqType}.
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

    Let job_has_completed_by := completed job_cost rate sched.

    (* ... iff any job j of tsk in this arrival sequence has
       completed by (job_arrival j + R). *)
    Definition is_response_time_bound_of_task :=
      forall (j: JobIn arr_seq),
        job_task j = tsk ->
        job_has_completed_by j (job_arrival j + R).
        
  End ResponseTimeBound.

  Section BasicLemmas.

    Context {sporadic_task: eqType}.
    Context {Job: eqType}.
    Variable job_cost: Job -> nat.
    Variable job_task: Job -> sporadic_task.

    Context {arr_seq: arrival_sequence Job}.
    
    (* Consider any valid schedule... *)
    Context {num_cpus : nat}.
    Variable sched: schedule num_cpus arr_seq.
    Variable rate: Job -> processor num_cpus -> nat.

    Let job_has_completed_by := completed job_cost rate sched.

    (* ... where jobs dont execute after completion. *)
    Hypothesis H_completed_jobs_dont_execute:
      completed_jobs_dont_execute job_cost rate sched.

    Section SpecificJob.

      (* Consider any job ...*)
      Variable j: JobIn arr_seq.
      
      (* ...with response-time bound R in this schedule. *)
      Variable R: time.
      Hypothesis response_time_bound:
        job_has_completed_by j (job_arrival j + R). 

      (* The service at any time t' after the response time is 0. *)
      Lemma service_at_after_job_rt_zero :
        forall t',
          t' >= job_arrival j + R ->
          service_at rate sched j t' = 0.
      Proof.
        rename response_time_bound into RT,
               H_completed_jobs_dont_execute into EXEC; ins.
        unfold is_response_time_bound_of_task, completed,
               completed_jobs_dont_execute in *.
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

      (* The cumulative service after the response time is 0. *)
      Lemma sum_service_after_job_rt_zero :
        forall t' t'',
          t' >= job_arrival j + R ->
          \sum_(t' <= t < t'') service_at rate sched j t = 0.
      Proof.
        ins; apply/eqP; rewrite -leqn0.
        rewrite big_nat_cond; rewrite -> eq_bigr with (F2 := fun i => 0);
          first by rewrite big_const_seq iter_addn mul0n addn0 leqnn.
        intro i; rewrite andbT; move => /andP [LE _].
        by rewrite service_at_after_job_rt_zero;
          [by ins | by apply leq_trans with (n := t')].
      Qed.
      
    End SpecificJob.
    
    Section AllJobs.

      (* Assume a task tsk ...*)
      Variable tsk: sporadic_task.

      (* ...and that R is a response-time bound of tsk in this schedule. *)
      Variable R: time.
      Hypothesis response_time_bound:
        is_response_time_bound_of_task job_cost job_task tsk rate sched R.

      Variable j: JobIn arr_seq.
      Hypothesis H_job_of_task: job_task j = tsk.

      (* The service at any time t' after the response time is 0. *)
      Lemma service_at_after_rt_zero :
        forall t',
          t' >= job_arrival j + R ->
          service_at rate sched j t' = 0.
      Proof.
        by ins; apply service_at_after_job_rt_zero with (R := R); [apply response_time_bound |].
      Qed.

      (* The cumulative service after the response time is 0. *)
      Lemma sum_service_after_rt_zero :
        forall t' t'',
          t' >= job_arrival j + R ->
          \sum_(t' <= t < t'') service_at rate sched j t = 0.
      Proof.
        by ins; apply sum_service_after_job_rt_zero with (R := R); [apply response_time_bound |].
      Qed.
      
    End AllJobs.

  End BasicLemmas.
    
End ResponseTime.