Require Import rt.util.all.
Require Import rt.model.time rt.model.arrival.basic.task rt.model.arrival.basic.job rt.model.arrival.basic.arrival_sequence
               rt.model.priority.
Require Import rt.model.schedule.uni.schedule rt.model.schedule.uni.workload.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Module Service.

  Import UniprocessorSchedule Priority Workload.

  (* In this section, we define the more general notion of service received by sets of jobs. *)
  Section ServiceOverSets.

    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.

    (* Consider any job arrival sequence... *)
    Variable arr_seq: arrival_sequence Job.

    (* ...and any uniprocessor schedule of these jobs. *)
    Variable sched: schedule Job.

    (* Let jobs denote any (finite) set of jobs. *)
    Variable jobs: seq Job. 

    Section Definitions.

      (* First, we define the service received by a generic set of jobs. *)
      Section ServiceOfJobs.

        (* Then, given any predicate over jobs, ...*)
        Variable P: Job -> bool.

        (* ...we define the cumulative service received during [t1, t2)
           by the jobs that satisfy this predicate. *)
        Definition service_of_jobs (t1 t2: time) :=
          \sum_(j <- jobs | P j) service_during sched j t1 t2.

      End ServiceOfJobs.

      (* Next, we define the service received by tasks with higher-or-equal
         priority under a given FP policy. *)
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
        Variable higher_eq_priority: JLFP_policy Job.

        (* Let j be the job to be analyzed. *)
        Variable j: Job.

        (* Based on the definition of jobs of higher or equal priority, ... *)
        Let of_higher_or_equal_priority j_hp := higher_eq_priority j_hp j.
       
        (* ...we define the service received during [t1, t2) by jobs of higher or equal priority. *)
        Definition service_of_higher_or_equal_priority_jobs (t1 t2: time) :=
          service_of_jobs of_higher_or_equal_priority t1 t2.

      End PerJobPriority.

    End Definitions.

    Section Lemmas.

      (* Let P be any predicate over jobs. *)
      Variable P: Job -> bool.

      (* In this section, we prove that the service received by any set of jobs
         is upper-bounded by the corresponding workload. *)
      Section ServiceBoundedByWorkload.

        (* Recall the definition of workload. *)
        Let workload_of := workload_of_jobs job_cost.

        (* Assume that jobs do not execute after completion.*)
        Hypothesis H_completed_jobs_dont_execute:
          completed_jobs_dont_execute job_cost sched.
        
        (* Then, we prove that the service received by those jobs is no larger than their workload. *)
        Lemma service_of_jobs_le_workload:
          forall t1 t2,
            service_of_jobs P t1 t2 <= workload_of jobs P.
        Proof.
          intros t1 t2.
          apply leq_sum; intros j _.
          by apply cumulative_service_le_job_cost.
        Qed.

      End ServiceBoundedByWorkload.

      (* In this section, we prove that the service received by any set of jobs
         is upper-bounded by the corresponding interval length. *)
      Section ServiceBoundedByIntervalLength.

        (* Assume that jobs do not execute after completion.*)
        Hypothesis H_completed_jobs_dont_execute:
          completed_jobs_dont_execute job_cost sched.

        (* Assume that the sequence of jobs is a set. *)
        Hypothesis H_no_duplicate_jobs: uniq jobs.
        
        (* Then, we prove that the service received by those jobs is no larger than their workload. *)
        Lemma service_of_jobs_le_delta:
          forall t1 t2,
            service_of_jobs P t1 t2 <= t2 - t1.
        Proof.
          unfold service_of_jobs; intros t1 t2.
          rewrite exchange_big /=.
          apply leq_trans with (n := \sum_(t1 <= t < t2) 1); last by simpl_sum_const.
          apply leq_sum; intros t _; rewrite /service_at.
          case (boolP (has (fun j => P j && scheduled_at sched j t) jobs)) => [HAS | ALL].
          {
            move: HAS => /hasP [j0 IN0 /andP [PRED0 SCHED0]].
            rewrite big_mkcond (bigD1_seq j0) //= PRED0 SCHED0 big1 //.
            intros j1 NEQ; case: ifP => PRED1; last by done.
            apply/eqP; rewrite eqb0; apply/negP; intro SCHED1.
            apply only_one_job_scheduled with (j2 := j1) in SCHED0; last by done.
            by rewrite SCHED0 eq_refl in NEQ.
          }
          {
            rewrite -all_predC in ALL; move: ALL => /allP ALL.
            rewrite big_seq_cond big1 //.
            move => j0 /andP [IN0 PRED0]; apply/eqP; rewrite eqb0.
            by specialize (ALL j0 IN0); rewrite /= PRED0 /= in ALL.
          }
        Qed.

      End ServiceBoundedByIntervalLength.
      
    End Lemmas.
    
  End ServiceOverSets.

End Service.