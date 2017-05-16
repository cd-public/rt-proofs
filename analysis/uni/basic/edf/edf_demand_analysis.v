Require Import rt.util.all.
Require Import rt.model.time rt.model.arrival.basic.job rt.model.arrival.basic.task rt.model.arrival.basic.arrival_sequence rt.model.priority.
Require Import rt.model.schedule.uni.schedule rt.model.schedule.uni.schedulability rt.model.schedule.uni.basic.platform.
Require Import rt.analysis.uni.basic.edf.total_service rt.analysis.uni.basic.edf.demand.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.

Module EDFDemandAnalysis.

  Import UniprocessorSchedule Schedulability Priority Platform Job Demand.

  (* In this section, we prove some useful lemmas about demand and
     schedules which respect EDF. *)

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
    (* ...and that jobs only execute after they arrived ... *)
    Hypothesis H_jobs_must_arrive_to_execute:
      jobs_must_arrive_to_execute job_arrival sched.
    (* ...and don't execute after they completed. *)
    Hypothesis H_completed_jobs_dont_execute:
      completed_jobs_dont_execute job_cost sched.

    (* For simplicity, let's define a function to check whether all
       deadlines have been met in a given schedule. *)
    Let no_deadline_miss_in (sched: schedule Job) :=
      forall j, job_misses_no_deadline job_arrival job_cost job_deadline sched j.

    (* For simplicity, let us define some local names about demand. *)
    Let absolute_deadline (j: Job) :=
      job_arrival j + job_deadline j.
    Let demand_during := total_demand_during job_arrival job_cost job_deadline arr_seq.
    Let demand_before := total_demand_before job_arrival job_cost job_deadline arr_seq.
    Let arrivals_and_deadline_between := jobs_with_arrival_and_deadline_between job_arrival job_deadline arr_seq.

    (* In this section, we prove that the demand gives a sufficient
       condition for schedulability under EDF. *)
    Section DemandUnderEDF.

      (* Let sched_edf be any EDF schedule ... *)
      Variable sched_edf: schedule Job.
      Check respects_JLFP_policy.
      Check EDF.
      Hypothesis H_edf_policy: respects_JLFP_policy job_arrival job_deadline arr_seq sched_edf (EDF job_arrival job_deadline).

      (* ...where jobs must arrive to execute. *)
      Hypothesis H_jobs_must_arrive_to_execute_sched_edf:
        jobs_must_arrive_to_execute job_arrival sched_edf.
                                                                               
      (* ...and don't execute after they completed. *)
      Hypothesis H_completed_jobs_dont_execute_sched_edf:
        completed_jobs_dont_execute job_cost sched_edf.

      (* If the demand during any interval is bounded by the length of the interval, ... *)
      Hypothesis H_demand_always_satisfied:
        forall t delta, demand_during t (t + delta) <= delta.

      (*...then no deadline is missed. *)

      Lemma schedulable_if_demand_always_satisfied:
        no_deadline_miss_in sched_edf.
      Proof.
        unfold no_deadline_miss_in. intros j.
        unfold job_misses_no_deadline. unfold completed_by.
        unfold respects_JLFP_policy, backlogged, pending in H_edf_policy.
        unfold EDF in H_edf_policy. unfold service, service_during.        
        rewrite -> big_cat_nat with (n := (job_arrival j)); [> | auto | apply leq_addr].

        
        Admitted.
    End DemandUnderEDF.

    (* Using the optimality of EDF, we prove the correctness of the
       demand-based, exact feasibility test. *)
    Section FeasibilityTest.

      (* First, we define the concept of feasibility of a job set. *)
      Let job_set_is_feasible :=
        exists sched,
          no_deadline_miss_in sched.

      (* Then, by testing whether the demand is satisfied for every
         interval, ... *)
      Let demand_is_satisfied :=
        forall t delta, demand_during t (t + delta) <= delta.

      (* ... we establish the exact feasibility analysis for
             uniprocessor scheduling. *)
      (* TODO: for now only stated. *)
      Theorem job_set_is_feasible_iff_demand_is_satisfied:
        job_set_is_feasible <->
        demand_is_satisfied.
      Proof.
        Admitted.
		
    End FeasibilityTest.

  End Lemmas.

End EDFDemandAnalysis.