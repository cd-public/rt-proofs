Require Import rt.util.all.
Require Import rt.model.time rt.model.task rt.model.job rt.model.arrival_sequence
               rt.model.priority.
Require Import rt.model.uni.schedule rt.model.uni.workload.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Module Service.

  Import UniprocessorSchedule Priority Workload.

  (* In this section, we define the more general notion of service received by sets of jobs. *)
  Section ServiceOverSets.

    Context {Job: eqType}.
    Variable job_cost: Job -> time.

    (* Consider any uniprocessor schedule. *)
    Context {arr_seq: arrival_sequence Job}.
    Variable sched: schedule arr_seq.

    (* Recall the sequence of job arrivals in any interval [t1, t2). *)
    Let arrivals_between := jobs_arrived_between arr_seq.

    Section Definitions.

      (* First, we define the service received by a generic set of jobs. *)
      Section ServiceOfJobs.

        (* Given any predicate over jobs, ...*)
        Variable P: JobIn arr_seq -> bool.

        (* ...we define the cumulative service received during [t1, t2)
           by the jobs that satisfy this predicate. *)
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
       
        (* ...we define the service received during [t1, t2) by jobs of higher or equal priority. *)
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
       
        (* ...we define the service received during [t1, t2) by jobs of higher or equal priority. *)
        Definition service_of_higher_or_equal_priority_jobs (t1 t2: time) :=
          service_of_jobs of_higher_or_equal_priority t1 t2.

      End PerJobPriority.

    End Definitions.

    Section Lemmas.

      (* In this section, we prove that the service received by any set of jobs
         is upper-bounded by the corresponding workload. *)
      Section ServiceBoundedByWorkload.

        (* Assume that jobs do not execute after completion.*)
        Hypothesis H_completed_jobs_dont_execute:
          completed_jobs_dont_execute job_cost sched.
        
        (* Recall the definition of workload. *)
        Let workload_of := workload_of_jobs job_cost arr_seq.

        (* Let P be any predicate over jobs. *)
        Variable P: Job -> bool.

        (* Then, we prove that the service received by those jobs is no larger than their workload. *)
        Lemma service_le_workload:
          forall t1 t2,
            service_of_jobs P t1 t2 <= workload_of P t1 t2.
        Proof.
          intros t1 t2.
          apply leq_sum; intros j _.
          by apply cumulative_service_le_job_cost.
        Qed.

      End ServiceBoundedByWorkload.

    End Lemmas.
    
  End ServiceOverSets.

End Service.