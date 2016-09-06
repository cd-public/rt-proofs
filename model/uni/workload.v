Require Import rt.util.all.
Require Import rt.model.time rt.model.task rt.model.job rt.model.arrival_sequence
               rt.model.priority.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Module Workload.

  Import Time ArrivalSequence Priority.

  (* In this section, we define the notion of workload for sets of jobs. *)  
  Section WorkloadDefs.

    Context {Task: eqType}.
    Context {Job: eqType}.
    Variable job_cost: Job -> time.
    Variable job_task: Job -> Task.
      
    (* Consider any job arrival sequence... *)
    Variable arr_seq: arrival_sequence Job.

    (* ...and recall the job arrivals in any interval [t1, t2). *)
    Let arrivals_between := jobs_arrived_between arr_seq.

    (* First, we define the workload for generic sets of jobs. *)
    Section WorkloadOfJobs.

      (* Given any predicate over Jobs, ... *)
      Variable pred: JobIn arr_seq -> bool.

      (* ...we define the total workload of the jobs released during [t1, t2)
         that satisfy such a predicate. *)
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
         higher-or-equal-priority tasks released in that interval. *)
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
         higher-or-equal priority released in that interval. *)
      Definition workload_of_higher_or_equal_priority_jobs (t1 t2: time) :=
        workload_of_jobs of_higher_or_equal_priority t1 t2.

    End PerJobPriority.
    
  End WorkloadDefs.

End Workload.