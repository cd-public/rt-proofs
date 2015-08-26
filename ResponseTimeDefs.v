Require Import Vbase TaskDefs JobDefs TaskArrivalDefs ScheduleDefs PlatformDefs helper
                ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Module ResponseTime.

  Import Schedule SporadicTaskset SporadicTaskArrival.

  Section ResponseTimeBound.

    Context {Job: eqType}.

    Variable job_task: Job -> sporadic_task.
  
    Variable num_cpus: nat.
    Variable rate: Job -> processor -> nat.
    Variable schedule_of_platform: schedule Job -> Prop.
  
    Variable tsk: sporadic_task.

    Definition job_has_completed_by (job_cost: Job -> nat) (sched: schedule Job) :=
      completed job_cost num_cpus rate sched.
    
    Definition response_time_ub_task (response_time_bound: time) :=
      forall (job_arrival: Job -> nat)
             (job_cost: Job -> nat)
             (sched: schedule Job) (j: Job),
        job_task j == tsk ->
        schedule_of_platform sched ->
        (* job_arrival and job_cost are valid -> *)
        job_has_completed_by job_cost sched j (job_arrival j + response_time_bound).

    Section BasicLemmas.

      Variable response_time_bound: time.
      Hypothesis is_response_time_bound:
        response_time_ub_task response_time_bound.

      Variable job_arrival: Job -> nat.
      Variable job_cost: Job -> nat.
      Variable sched: schedule Job.
      Hypothesis platform: schedule_of_platform sched.

      Variable j: Job.
      Hypothesis job_of_task: job_task j == tsk.

      Hypothesis comp_jobs_dont_exec:
        completed_job_doesnt_exec job_cost num_cpus rate sched.

      Lemma service_at_after_rt_zero :
        forall t' (GE: t' >= job_arrival j + response_time_bound),
          service_at num_cpus rate sched j t' = 0.
      Proof.
        rename response_time_bound into R, is_response_time_bound into RT,
               comp_jobs_dont_exec into EXEC; ins.
        unfold response_time_ub_task, completed,
               completed_job_doesnt_exec in *.
        specialize (RT job_arrival job_cost sched j job_of_task platform).
        apply/eqP; rewrite -leqn0.
        rewrite <- leq_add2l with (p := job_cost j).
        move: RT => /eqP RT; rewrite -{1}RT addn0.
        apply leq_trans with (n := service num_cpus rate sched j t'.+1); last by apply EXEC.
        unfold service; rewrite -> big_cat_nat with (p := t'.+1) (n := job_arrival j + R);
          [rewrite leq_add2l /= | by ins | by apply ltnW].
        by rewrite big_nat_recr // /=; apply leq_addl.
      Qed.

      Lemma sum_service_after_rt_zero :
        forall t' (GE: t' >= job_arrival j + response_time_bound) t'',
          \sum_(t' <= t < t'') service_at num_cpus rate sched j t = 0.
      Proof.
        ins; apply/eqP; rewrite -leqn0.
        rewrite big_nat_cond; rewrite -> eq_bigr with (F2 := fun i => 0);
          first by rewrite big_const_seq iter_addn mul0n addn0 leqnn.
        intro i; rewrite andbT; move => /andP [LE _].
        by rewrite service_at_after_rt_zero; [by ins | by apply leq_trans with (n := t')].
      Qed.

    End BasicLemmas.
    
    Section LowerBoundOfResponseTimeBound.

      Import Job.
      
      Variable response_time_bound: time.
      Hypothesis is_response_time_bound:
        response_time_ub_task response_time_bound.
      
      Hypothesis set_of_jobs_nonempty:
        exists j: Job, job_task j == tsk.

      Hypothesis rate_at_most_one:
        forall (j: Job) (cpu: processor), rate j cpu <= 1.

      Lemma response_time_ub_ge_cost: response_time_bound >= task_cost tsk.
      Proof.
        unfold response_time_ub_task, valid_sporadic_task,
               job_has_completed_by, completed in *;
        rename set_of_jobs_nonempty into EX, is_response_time_bound into BOUND,
               response_time_bound into R; des.
        set myarr := fun (j: Job) => 0.
        
        set mysched := fun (cpu: processor) (t: time) =>
                          if cpu == 0 then
                            (if t < task_cost (job_task j) then Some j else None)
                          else None.

        assert (PLAT: schedule_of_platform mysched). admit.

        set mycost := fun (j: Job) => task_cost (job_task j).
        specialize (BOUND myarr mycost mysched j EX PLAT).
        move: EX => /eqP EX.
        move: BOUND; rewrite eqn_leq; move => /andP [_ LE].
        
        apply leq_trans with (n := service num_cpus rate mysched j (myarr j + R));
          first by unfold mycost in LE; rewrite EX in LE.

        unfold service, service_at, myarr, mysched.
        rewrite exchange_big_nat /=.
        destruct num_cpus; first by rewrite big_geq //.
        rewrite big_nat_recl // /=.
        rewrite -> eq_big_nat with (n := n) (F2 := fun i => 0);
          last by ins; rewrite -> eq_big_nat with (F2 := fun i => 0);
            by ins; rewrite big_const_nat iter_addn mul0n addn0.
        rewrite big_const_nat iter_addn mul0n 2!addn0.
        apply leq_trans with (n := \sum_(0 <= i < 0 + R) 1);
          last by rewrite big_const_nat iter_addn subn0 add0n mul1n addn0 leqnn.
        apply leq_sum; ins.
        rewrite -[1]muln1; apply leq_mul; [by apply leq_b1 | by apply rate_at_most_one].
      Qed.

    End LowerBoundOfResponseTimeBound.
    
  End ResponseTimeBound.
  
End ResponseTime.