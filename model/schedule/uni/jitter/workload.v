Require Import rt.util.all.
Require Import rt.model.time rt.model.arrival.basic.task rt.model.arrival.basic.job rt.model.priority.
Require Import rt.model.arrival.jitter.arrival_sequence.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

(* In this file, we define the workload requested by jobs with
   actual arrival time (including jitter) in a given interval. *)
Module Workload.

  Import Time ArrivalSequenceWithJitter Priority.

  (* First, we define the notion of workload for sets of jobs. *)  
  Section WorkloadDefs.

    Context {Task: eqType}.
    Context {Job: eqType}.
    Variable job_cost: Job -> time.
    Variable job_jitter: Job -> time.
    Variable job_task: Job -> Task.
      
    (* Consider any job arrival sequence... *)
    Variable arr_seq: arrival_sequence Job.

    (* ...and recall the actual job arrivals in a given interval [t1, t2). *)
    Let arrivals_between := actual_arrivals_between job_jitter arr_seq.

    (* First, we define the workload for generic sets of jobs. *)
    Section WorkloadOfJobs.

      (* Given any predicate over Jobs, ... *)
      Variable pred: JobIn arr_seq -> bool.

      (* ...we define the total workload of the jobs with actual arrival time
         in [t1, t2) that satisfy such a predicate. *)
      Definition workload_of_jobs (t1 t2: time) :=
        \sum_(j <- arrivals_between t1 t2 | pred j) job_cost j.

    End WorkloadOfJobs.

    (* Then, we define the workload of tasks with higher or equal priority
       under FP policies. *)
    Section PerTaskPriority.

      (* Consider any FP policy that indicates whether a task has
         higher or equal priority. *)
      Variable higher_eq_priority: FP_policy Task.

      (* Let tsk be the task to be analyzed. *)
      Variable tsk: Task.

      (* Recall the notion of a job of higher or equal priority. *)
      Let of_higher_or_equal_priority j :=
        higher_eq_priority (job_task j) tsk.
      
      (* Then, we define the workload of higher or equal priority requested
         in the interval [t1, t2) as the workload of all the jobs of
         higher-or-equal-priority tasks with actual arrival time in that interval. *)
      Definition workload_of_higher_or_equal_priority_tasks (t1 t2: time) :=
        workload_of_jobs of_higher_or_equal_priority t1 t2.

    End PerTaskPriority.

    (* Then, we define the workload of jobs with higher or equal priority
       under JLFP policies. *)
    Section PerJobPriority.

      (* Consider any JLFP policy that indicates whether a job has
         higher or equal priority. *)
      Variable higher_eq_priority: JLFP_policy arr_seq.

      (* Let j be the job to be analyzed. *)
      Variable j: JobIn arr_seq.

      (* Recall the notion of a job of higher or equal priority. *)
      Let of_higher_or_equal_priority j_hp := higher_eq_priority j_hp j.
      
      (* Then, we define the workload of higher or equal priority requested
         in the interval [t1, t2) as the workload of all the jobs of
         higher-or-equal priority with actual arrival time in that interval. *)
      Definition workload_of_higher_or_equal_priority_jobs (t1 t2: time) :=
        workload_of_jobs of_higher_or_equal_priority t1 t2.

    End PerJobPriority.
    
  End WorkloadDefs.

End Workload.