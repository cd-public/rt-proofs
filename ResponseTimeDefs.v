Require Import Vbase TaskDefs JobDefs TaskArrivalDefs ScheduleDefs PlatformDefs helper
                ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Module ResponseTime.

  Import Schedule SporadicTaskset SporadicTaskArrival.

  Section ResponseTimeBound.
    

    Context {Job: eqType}.
    Context {Processor : nat}.

    (* A response-time bound always applies with regard to some set of
    considered schedules, e.g., "all global EDF schedules".  This
    Prop checks whether a schedule is valid with regard to the
    considered class. *)
    Variable is_a_valid_schedule: schedule Job -> Prop.

    (* Given a task ...*)
    Variable tsk: sporadic_task.

    (* ...and a response-time bound R... *)
    Variable R: time.

    (* ... it is a valid response-time bound of tsk if... *)
    Variable j : Job.
    Variable job_task: Job -> sporadic_task.

    (* ...for any job of tsk... *) 
    Hypothesis H_is_a_job_of_tsk: job_task j == tsk.

    (*...in any valid schedule...*)
    Variable sched: schedule Job.
    Hypothesis H_is_a_valid_schedule: is_a_valid_schedule sched.

    (*...the job remains pending no longer than specified by the bound.*)
    Variable job_arrival: Job -> nat.
    Variable job_cost: Job -> nat.
    Variable rate: Job -> Processor -> nat.
    
    Definition job_has_completed_by :=
      completed job_cost rate sched.


    Definition is_a_valid_response_time_bound :=
      job_has_completed_by job_cost sched j (job_arrival j + R).



    

    Definition response_time_is_bounded :=
      job_task j == tsk ->

      (* job_arrival and job_cost are valid -> *)
      job_has_completed_by j (job_arrival j + response_time_bound).
      
    
    Definition response_time_ub_task (response_time_bound: time) :=
      forall (job_arrival: Job -> nat)
             (job_cost: Job -> nat)
             (sched: schedule Job) (j: Job),
         ->

        (* job_arrival and job_cost are valid -> *)
        

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
    
  End ResponseTimeBound.

  Section LowerBoundOfResponseTimeBound.

    Context {Job: eqType}.

    Variable job_task: Job -> sporadic_task.
  
    Variable num_cpus: nat.
    Variable rate: Job -> processor -> nat.
    Variable schedule_of_platform: schedule Job -> Prop.

    Hypothesis rate_at_most_one:
      forall (j: Job) (cpu: processor), rate j cpu <= 1.

    Variable tsk: sporadic_task.
    Hypothesis job_of_tsk_exists:
      exists j: Job, job_task j == tsk.

    Variable response_time_bound: time.
    Hypothesis is_response_time_bound:
      response_time_ub_task job_task num_cpus rate
                            schedule_of_platform tsk response_time_bound.
      
    Lemma response_time_ub_ge_cost: response_time_bound >= task_cost tsk.
    Proof.
      unfold response_time_ub_task, valid_sporadic_task,
             job_has_completed_by, completed in *.
      rename job_of_tsk_exists into EX,
             is_response_time_bound into BOUND,
             response_time_bound into R; des.

      set myarr := fun (j': Job) =>
                     if j' == j then 0
                     else task_cost tsk + 1.
      
      set mysched :=
        fun (cpu: processor) (t: time) =>
          if cpu == 0 then
            (if t < task_cost (job_task j) then Some j else None)
          else None.

      set mycost := fun (j: Job) => task_cost (job_task j).

      assert (PLAT: schedule_of_platform mysched). admit.

      specialize (BOUND myarr mycost mysched j EX PLAT).
      move: EX => /eqP EX.
      move: BOUND; rewrite eqn_leq; move => /andP [_ LE].
        
      apply leq_trans with (n := service num_cpus rate mysched j (myarr j + R));
        first by unfold mycost in LE; rewrite EX in LE.

      unfold service, service_at, myarr, mysched; rewrite eq_refl.
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
    
End ResponseTime.

Section bla. 

  Variable Job: eqType.
  Variable job_arrival: Job -> time.

  Variable arrival_seq: time -> seq Job.

  Hypothesis arrival_sequence_equiv_job_arrival :
    forall j t, j \in (arrival_seq t) <-> job_arrival j == t.

  Hypothesis arrival_sequence_is_set :
    forall t, uniq (arrival_seq t).

  (* Given a job set, this allows:
     1) define an arrival sequence and job_arrival functions
        for the jobs in Job.
     2) doesn't allow creating a new arrival sequence *)

End bla.

Section bla2.

  Import SporadicTask.
  
  Variable Job: eqType. (* Job universe *)
  Variable job_task: Job -> sporadic_task.

  Definition arrival_sequence := time -> seq Job.

  Definition arrives_in (j: Job) (arr: arrival_sequence) :=
    exists t, j \in arr t.

  Definition equiv_arrival_seq (job_arrival: Job -> time)
                               (arr: arrival_sequence) :=
    forall j,
      arrives_in j arr ->
      (forall t, j \in arr t <-> job_arrival j == t).

  Definition sporadic_task_model (job_arrival: Job -> time)
                                 (arr: arrival_sequence) :=
    forall j j',
           j <> j' -> (* Given two different jobs j and j' such that *)
           arrives_in j arr -> (* j arrives *)
           arrives_in j' arr -> (* j' arrives *)
           job_task j = job_task j' -> (* they are from the same task *)
           job_arrival j <= job_arrival j' -> (* and j arrives before j' *)
      (* then they are separated by the period. *)
      job_arrival j' >= job_arrival j + task_period (job_task j).


  Variable j: Job.
  Lemma bla : exists arrival_sequence job_arrival,
                arrives_in j arrival_sequence /\
                job_arrival j = 0 /\
                equiv_arrival_seq job_arrival arrival_sequence.
  Proof.
    set arr := fun t => if t == 0 then [::j] else [::].
    set job_arrival := fun (j: Job) => 0.
    exists arr, job_arrival; split;
      first by unfold arrives_in,arr; exists 0; rewrite eq_refl mem_seq1 eq_refl.
    split; first by unfold job_arrival.
    unfold equiv_arrival_seq; ins.
    unfold job_arrival, arr, arrives_in in *; des.
    rewrite [0 == t]eq_sym; split; ins;
    destruct (t == 0); destruct (t0 == 0); eauto.
    by rewrite in_nil in H.
  Qed.

  Variable job_arrival: Job -> time.
  Variable arr: arrival_sequence.
  Hypothesis equivalence: equiv_arrival_seq job_arrival arr.
  Hypothesis sporadic: sporadic_task_model job_arrival arr.  

End bla2.

Section bla3.

  Import SporadicTask.
  
  Variable Job: eqType. (* Job universe *)
  Variable job_cost: Job -> nat.
  Variable job_deadline: Job -> nat.
  Variable job_task: Job -> sporadic_task.

  Record JobIn (arr_seq: arrival_sequence Job) : Type :=
  {
    JobIn_job: Job;
    JobIn_arrival_time: time;
    JobIn_proof_of_arrival: JobIn_job \in arr_seq JobIn_arrival_time
  }.
  
  Coercion job_of {arr: arrival_sequence Job} (j: JobIn arr) :=
    JobIn_job arr j.

  Definition job_arrival {arr: arrival_sequence Job} (j: JobIn arr) :=
    JobIn_arrival_time arr j.

  Section Test1.

    Variable arr: arrival_sequence Job.
    Variable j1 j2 j3: JobIn arr.
    Variable random_job: Job.
  
    Check (job_arrival j1).
    Check (job_cost j1).
    Check (job_cost random_job).
    Fail (job_arrival random_job).

    Check (arr 0).
    Check ((job_of j1) \in (arr 0)).
    (* Check (j1 \in arr 0). *)

  End Test1.
  
  Section Test2.

    Variable arr: arrival_sequence Job.
    Variable j: JobIn arr.

    Definition arrived_between t1 t2 := t1 <= job_arrival j <= t2.
    
  End Test2.

  Section ArrivalProperties.

    Import SporadicTaskset.
    
    Variable ts: sporadic_taskset.
    Variable arr_seq: arrival_sequence Job.

    Definition all_jobs_from_taskset :=
      forall (j: JobIn arr_seq), job_task j \in ts.

    Definition synchronous_release :=
      all_jobs_from_taskset /\
      forall (tsk: sporadic_task),
        tsk \in ts ->
          exists !(j: JobIn arr_seq), job_arrival j = 0.

    Lemma test : synchronous_release -> True.
    Proof.
      intro SYNC.
      unfold synchronous_release in SYNC; des.
      unfold unique in SYNC0.
    Admitted.

  End ArrivalProperties.

  Section Schedule.

    Require Import ScheduleDefs.
    Import SporadicTaskset Schedule.
    
    Record MyJob :=
    {
      myjob_index : nat;
      myjob_cost: nat;
      myjob_deadline: nat;
      myjob_task: sporadic_task               
    }.

    Definition my_ts := [ :: (3, 5, 5) ; (5, 10, 10)].
    Definition nth_elem x := nth (0,0,0) my_ts x.
    
    Definition create_sync_arrival (ts: sporadic_taskset) :=
      fun t =>
        if t == 0 then
          map (fun x => Build_MyJob
                        x
                        (task_cost (nth_elem x))
                        (task_deadline (nth_elem x))
                        (nth_elem x))
              (iota 0 (size my_ts))
        else [::].

    Check (create_sync_arrival my_ts).


    
    Definition my_cost (j: my_Job) :=
      if j == j1 then 2
      else if j == j2 then 4
      else 0.

    Definition my_deadline (j: my_Job) :=
      if j == j1 then 5
      else if j == j2 then 10
      else 0.

    Definition my_task (j: my_Job) :=
      
               
    
    cost_deadline_task
    iota 0 (size my_ts).

    Definition my
    
    Check (map (fun tsk => 1)).
    
  End Schedule.
  
End bla3.



























  
     (* Problems:
         1) We cannot create a set of jobs with only j.
            If there are other jobs, how do we define the schedule
            function for them?
            If we only schedule j, this schedule won't be work-conserving
            for the other jobs.
 
        2) The schedule function has to satisfy all the constraints
           specified by its platform (e.g. affinities). Otherwise, we need
           to prove one lemma for each platform.
            
           We can avoid constructing the schedule if we have this:

           Defininition valid_platform (plat: platform):
             for every arrival sequence,
               exists schedule that satisfies the constraints
               of the platform.

           That is to be proved for each platform.

      *)










(*

forall jobsets, forall tasks, forall sched, forall R, R is bertogna bound,
           then forall j response time of j <= R.

forall tasksets, forall R, R is solution of Bertogna's equation,
               forall arrival sequence, forall sched, forall j,
                                                 resp j <= R.

*)