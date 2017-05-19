Require Import rt.util.all.
Require Import rt.model.time rt.model.arrival.basic.job rt.model.arrival.basic.task rt.model.arrival.basic.arrival_sequence rt.model.priority.
Require Import rt.model.schedule.uni.schedule rt.model.schedule.uni.schedulability rt.model.schedule.uni.basic.platform.
Require Import rt.analysis.uni.basic.edf.total_service.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.


Module Demand.

  Import UniprocessorSchedule Schedulability Priority Platform Job TotalService.

  (* In this section, we define the concept of demand. *)
  Section DefiningDemand.

    Context {Task: eqType}.
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_deadline: Job -> time.
    Variable job_task: Job -> Task.

    (* Consider any job arrival sequence. *)
    
    Variable arr_seq: arrival_sequence Job.

    (* For simplicity, let us define some local variables.*)
    Let absolute_deadline (j: Job) :=
      job_arrival j + job_deadline j.

    (* In order to get all jobs which arrived and have to complete
       before t, we first define a function which filters
       the arrival sequence accordingly. *)
    Definition jobs_with_deadline_before t :=
      [seq j <- jobs_arrived_up_to arr_seq t | absolute_deadline j < t].
   
    (* Then we filter out jobs that haven't arrived before the start of an interval *)
    Definition jobs_with_arrival_and_deadline_between t1 t2 :=
      [seq j <- jobs_with_deadline_before t2 | (arrived_between job_arrival j t1 t2)].
 
    (* In this section, we define the demand of a given set of jobs. *)
    Section TotalDemand.

      (* Let us define the total demand in the interval [t1,t2) as the
         workload of jobs with arrival and deadline inside the interval.*)
      Definition total_demand_during t1 t2 :=
        \sum_(j <- jobs_with_arrival_and_deadline_between t1 t2) job_cost j.

      (* Similarly, the total demand before t is the demand in the interval [0, t). *)
      Definition total_demand_before t :=
        total_demand_during 0 t.

    End TotalDemand.

    (* In this section, we define the demand of a given task. *)
    Section DemandOfTask.

      (* Let tsk be any task ... *)
      Variable tsk: Task.

      (* ...and recall the predicate indicating whether a job
            is spawned by tsk. *)
      Let job_of_tsk (j: Job) := job_task j == tsk.

      (* In order to get all jobs of tsk which arrived and
         have to complete during [t1, t2), we filter the list
         we defined above accordingly. *)
      Definition jobs_of_task_with_arrival_and_deadline_between t1 t2 :=
        [seq j <- jobs_with_arrival_and_deadline_between t1 t2 | job_of_tsk j].

      (* Then let us define the processor demand of a task in the
         interval [t1,t2) as the workload of jobs of tsk with
         arrival and deadline inside this interval. *)
      Definition total_task_demand_during t1 t2 :=
	    \sum_(j <- jobs_of_task_with_arrival_and_deadline_between t1 t2) job_cost j.

	  (* The total demand of a task up to time t can be defined
		 as the total demand of tsk from 0 to t. *)
	  Definition total_task_demand_before t :=
		total_task_demand_during 0 t.

	End DemandOfTask.

  End DefiningDemand.

  (* In this section, we prove some useful lemmas about demand. *)
  Section Lemmas.

	Context {Task: eqType}.
	Context {Job: eqType}.
        Variable job_arrival: Job -> time.
	Variable job_cost: Job -> time.
	Variable job_deadline: Job -> time.
	Variable job_task: Job -> Task.


	(* Consider any job arrival sequence with no duplicate jobs... *)
	Context {arr_seq: arrival_sequence Job}.
	Hypothesis H_arrival_sequence_is_a_set:
	  arrival_sequence_is_a_set arr_seq.

	(* ... and any schedule of this arrival sequence. *)
	Variable sched: schedule Job.

	(* Assume that all jobs have valid job parameter and... *)
	Hypothesis H_valid_job_parameters:
	  forall (j: Job),
	    valid_realtime_job job_cost job_deadline j.

         (* Assume that job arrival times are consistent. *)
        Hypothesis H_arrival_times_are_consistent:
          arrival_times_are_consistent job_arrival arr_seq.

	(* ...and that jobs only execute after they arrived ... *)
        Check jobs_must_arrive_to_execute.
	Hypothesis H_jobs_must_arrive_to_execute:
	  jobs_must_arrive_to_execute job_arrival sched.
	(* ...and don't execute after they completed. *)
	Hypothesis H_completed_jobs_dont_execute:
	  completed_jobs_dont_execute job_cost sched.

	(* For simplicity, let's define a function to check whether all
	   deadlines have been met in a given schedule. *)
        Check job_misses_no_deadline.
	Let no_deadline_miss_in (sched: schedule Job) :=
	  forall j:Job, job_misses_no_deadline job_arrival job_cost job_deadline sched j.

	(* For simplicity, let us define some local names about demand. *)
	Let absolute_deadline (j: Job) :=
	  job_arrival j + job_deadline j.
        Check total_demand_during.
	Let demand_during := total_demand_during job_arrival job_cost job_deadline arr_seq.
	Let demand_before := total_demand_before job_arrival job_cost job_deadline arr_seq.
	Let arrivals_and_deadline_between := jobs_with_arrival_and_deadline_between job_arrival job_deadline arr_seq.

	(* In this section, we prove properties for the demand
	   for a specific job if the job set is schedulable. *)
	Section ConcreteJob.

	  (* Let t and delta define the interval [t, t + delta). *)
	  Variable t delta : time.

	  (* Let j be any job from the arrival_sequence ... *)
	  Variable j : Job.
	  (* ...whose arrival and deadline is in [t, t + delta). *)
          Hypothesis H_jobs_arrival_at_or_after_t:
            t <= job_arrival j.
          Hypothesis H_jobs_abs_deadline:
            absolute_deadline j <= t + delta.

	  (* If the job set is schedulable, ... *)
	  Hypothesis H_is_schedulable:
	    no_deadline_miss_in sched.

	  (* ...then we prove that j has completed by (t + delta). *)
	  Lemma jobs_in_interval_completed_by_the_end:
	    completed_by job_cost sched j (t + delta).
          Proof.
            unfold no_deadline_miss_in, job_misses_no_deadline in *.
            unfold absolute_deadline in *.
            by apply completion_monotonic with (t0 := job_arrival j + job_deadline j).
          Qed.

          Lemma split_service:
            forall n m, n <= m -> service sched j m = service sched j n + service_during sched j n m.
          Proof.
            intros n m; unfold service, service_during; move => H_in_range.
            rewrite -> big_cat_nat with (n := n); [> auto | auto | apply H_in_range].
          Qed.

          Lemma zero_service_prior_arrival:
            service sched j (job_arrival j) = 0.
          Proof.
            unfold service, service_during.
            rewrite (cumulative_service_before_job_arrival_zero job_arrival); [auto | apply H_jobs_must_arrive_to_execute | auto].
          Qed.  
          
          Lemma zero_service_prior_to_interval:
            service sched j t = 0.
          Proof.
            unfold service, service_during.
            rewrite (cumulative_service_before_job_arrival_zero job_arrival); [auto | apply H_jobs_must_arrive_to_execute | apply H_jobs_arrival_at_or_after_t].
          Qed.

          Lemma service_during_interval_is_service:
            service sched j (t + delta) = service_during sched j t (t + delta).
          Proof.
            rewrite -> split_service with (n := t); [> | apply leq_addr].
            rewrite -> zero_service_prior_to_interval; auto.
          Qed.
          
          Lemma service_at_deadline_is_cost:
            service sched j (absolute_deadline j) = job_cost j.
          Proof.
            unfold job_misses_no_deadline, completed_by in no_deadline_miss_in.
            replace (absolute_deadline j) with (job_arrival j + job_deadline j); [> apply/eqP; auto | auto].
          Qed.

          Lemma service_after_deadline_ge_cost:
            forall n, n >= (absolute_deadline j) -> job_cost j <= service sched j n.
          Proof.
            intros n; move => H_after_deadline.
            rewrite -> split_service with (n := absolute_deadline j); [> | auto].
            rewrite -> service_at_deadline_is_cost; apply leq_addr.
          Qed.
          
	  (* As a corollary, we can show that the service of j during
	     [t, t + delta) is equal to its cost. *)
	  Corollary service_jobs_in_interval_eq_cost:
	    service_during sched j t (t  = job_cost j.
          Proof.
            assert (GE: job_cost j <= service sched j (t + delta)).
            {
              apply service_after_deadline_ge_cost; auto.
            }
            rewrite <- service_during_interval_is_service; apply/eqP; rewrite -> eqn_leq; auto.
          Qed.
          
	End ConcreteJob.

	(* In this section we show properties that hold for
	   the total demand if no deadline is missed. *)

	Section Schedulability.

	  (* Assume that no deadline is missed by any job. *)
	  Hypothesis H_no_deadline_miss:
	    no_deadline_miss_in sched.

	  (* Since no deadline is missed, the total demand during any
		 interval is bounded by the total service in this interval. *)
	  Lemma total_service_ge_total_demand_if_schedulable:
	    forall (t:time) (d:time), demand_during t (t + d) <= total_service_during sched t (t + d).
          Proof.
            intros t d.
          Admitted.

	  (* It follows that, in any interval, the demand never exceeds the length of the interval. *)
	  Corollary demand_never_exceeds_time_if_schedulable:
	    forall t delta, demand_during t (t + delta) <= delta.
          Proof.
            intros t delta.
            rewrite -> leq_trans with (n := (total_service_during sched t (t + delta))). auto.
            apply total_service_ge_total_demand_if_schedulable.
            apply total_service_bounded_by_interval_length.
          Qed.

	End Schedulability.

  End Lemmas.

End Demand.