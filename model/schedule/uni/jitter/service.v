Require Import rt.util.all.
Require Import rt.model.time rt.model.arrival.basic.task rt.model.arrival.basic.job rt.model.arrival.basic.arrival_sequence
               rt.model.priority.
Require Import rt.model.schedule.uni.jitter.schedule.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

(* In this file, we define the service received by jobs with
   actual arrival time (including jitter) in a given interval. *)
Module Service.

  Import UniprocessorScheduleWithJitter Priority.

  (* First, we define the more general notion of service received by sets of jobs. *)
  Section ServiceOverSets.

    Context {Job: eqType}.
    Variable job_cost: Job -> time.
    Variable job_jitter: Job -> time.

    (* Consider any uniprocessor schedule. *)
    Context {arr_seq: arrival_sequence Job}.
    Variable sched: schedule arr_seq.

    (* Recall the actual job arrivals in a given interval [t1, t2). *)
    Let arrivals_between := actual_arrivals_between job_jitter arr_seq.

    Section Definitions.

      (* First, we define the service received by a generic set of jobs. *)
      Section ServiceOfJobs.

        (* Given any predicate over jobs, ...*)
        Variable P: JobIn arr_seq -> bool.

        (* ...we define the cumulative service received by jobs with actual
           arrival time in [t1, t2) that such a predicate. *)
        Definition service_of_jobs (t1 t2: time) :=
          \sum_(j <- arrivals_between t1 t2 | P j) service_during sched j t1 t2.

      End ServiceOfJobs.

      (* Then, we define the service received by tasks with higher or equal priority
         under FP policies. *)
      Section PerTaskPriority.

        Context {Task: eqType}.
        Variable job_task: Job -> Task.

        (* Consider any FP policy. *)
        Variable higher_eq_priority: FP_policy Task.

        (* Let tsk be the task to be analyzed. *)
        Variable tsk: Task.

        (* Based on the definition of jobs of higher or equal priority (with respect to tsk), ... *)
        Let of_higher_or_equal_priority j := higher_eq_priority (job_task j) tsk.
       
        (* ...we define the service received by jobs of higher-or-equal-priority
           tasks with actual arrival time in [t1, t2). *)
        Definition service_of_higher_or_equal_priority_tasks (t1 t2: time) :=
          service_of_jobs of_higher_or_equal_priority t1 t2.

      End PerTaskPriority.
      
      (* Next, we define the service received by jobs with higher or equal priority
         under JLFP policies. *)
      Section PerJobPriority.

        (* Consider any JLDP policy. *)
        Variable higher_eq_priority: JLFP_policy arr_seq.

        (* Let j be the job to be analyzed. *)
        Variable j: JobIn arr_seq.

        (* Based on the definition of jobs of higher or equal priority, ... *)
        Let of_higher_or_equal_priority j_hp := higher_eq_priority j_hp j.
       
        (* ...we define the service received by jobs of higher or equal priority
           with actual arrival time in [t1, t2). *)
        Definition service_of_higher_or_equal_priority_jobs (t1 t2: time) :=
          service_of_jobs of_higher_or_equal_priority t1 t2.

      End PerJobPriority.

    End Definitions.

  End ServiceOverSets.

End Service.