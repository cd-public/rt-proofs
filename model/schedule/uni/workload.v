Require Import rt.util.all.
Require Import rt.model.time rt.model.arrival.basic.task rt.model.arrival.basic.job rt.model.arrival.basic.arrival_sequence
               rt.model.priority.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Module Workload.

  Import Time ArrivalSequence Priority.

  (* In this section, we define the notion of workload for sets of jobs. *)  
  Section WorkloadDefs.

    Context {Task: eqType}.
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_task: Job -> Task.
      
    (* Consider any job arrival sequence... *)
    Variable arr_seq: arrival_sequence Job.

    (* ...and any (finite) set of jobs. *)
    Variable jobs: seq Job.

    (* First, we define the workload for generic sets of jobs. *)
    Section WorkloadOfJobs.

      (* Given any predicate over Jobs, ... *)
      Variable P: Job -> bool.

      (* ...we define the total workload of the jobs that satisfy such a predicate. *)
      Definition workload_of_jobs := \sum_(j <- jobs | P j) job_cost j.

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
      
      (* Then, we define the workload of all jobs of tasks with
         higher-or-equal priority than tsk. *)
      Definition workload_of_higher_or_equal_priority_tasks :=
        workload_of_jobs of_higher_or_equal_priority.

    End PerTaskPriority.

    (* Then, we define the workload of jobs with higher or equal priority
       under JLFP policies. *)
    Section PerJobPriority.

      (* Consider any JLFP policy that indicates whether a job has
         higher or equal priority. *)
      Variable higher_eq_priority: JLFP_policy Job.

      (* Let j be the job to be analyzed. *)
      Variable j: Job.

      (* Recall the notion of a job of higher or equal priority. *)
      Let of_higher_or_equal_priority j_hp := higher_eq_priority j_hp j.
      
      (* Then, we define the workload of higher or equal priority of all jobs
         with higher-or-equal priority than j. *)
      Definition workload_of_higher_or_equal_priority_jobs :=
        workload_of_jobs of_higher_or_equal_priority.

    End PerJobPriority.
    
  End WorkloadDefs.

End Workload.