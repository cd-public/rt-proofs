Require Import rt.util.all.
Require Import rt.model.job rt.model.task rt.model.priority rt.model.task_arrival
               rt.model.arrival_bounds.
Require Import rt.model.uni.schedule_of_task rt.model.uni.workload
               rt.model.uni.schedulability rt.model.uni.response_time
               rt.model.uni.service.
Require Import rt.model.uni.basic.busy_interval rt.model.uni.basic.platform.
Require Import rt.analysis.uni.basic.workload_bound_fp.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Module ResponseTimeAnalysisFP.

  Import Job ScheduleOfTask SporadicTaskset Priority ResponseTime
         TaskArrival ArrivalBounds WorkloadBoundFP Platform Schedulability
         BusyInterval Workload Service.

  (* In this section, we prove that any fixed point in the RTA for uniprocessor
     FP scheduling is a response-time bound. *)
  Section ResponseTimeBound.

    Context {SporadicTask: eqType}.
    Variable task_cost: SporadicTask -> time.
    Variable task_period: SporadicTask -> time.
    Variable task_deadline: SporadicTask -> time.
    
    Context {Job: eqType}.
    Variable job_cost: Job -> time.
    Variable job_deadline: Job -> time.
    Variable job_task: Job -> SporadicTask.
    
    (* Assume any job arrival sequence without duplicates... *)
    Context {arr_seq: arrival_sequence Job}.
    Hypothesis H_no_duplicate_arrivals: arrival_sequence_is_a_set arr_seq.
    
    (* ... in which jobs arrive sporadically and have valid parameters. *)
    Hypothesis H_sporadic_tasks:
      sporadic_task_model task_period arr_seq job_task.
    Hypothesis H_valid_job_parameters:
      forall (j: JobIn arr_seq),
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j.

    (* Consider a task set ts where all tasks have valid parameters... *)
    Variable ts: seq SporadicTask.
    Hypothesis H_valid_task_parameters:
      valid_sporadic_taskset task_cost task_period task_deadline ts.

    (* ... and assume that all jobs in the arrival sequence come from the task set. *)
    Hypothesis H_all_jobs_from_taskset:
      forall (j: JobIn arr_seq), job_task j \in ts.

    (* Next, consider any uniprocessor schedule such that...*)
    Variable sched: schedule arr_seq.

    (* ...jobs do not execute before their arrival times nor longer than their
       execution costs. *)
    Hypothesis H_jobs_must_arrive_to_execute:
      jobs_must_arrive_to_execute sched.
    Hypothesis H_completed_jobs_dont_execute:
      completed_jobs_dont_execute job_cost sched.

    (* Consider an FP policy that indicates a higher-or-equal priority relation,
       and assume that the relation is reflexive and transitive. *)
    Variable higher_eq_priority: FP_policy SporadicTask.
    Hypothesis H_priority_is_reflexive: FP_is_reflexive higher_eq_priority.
    Hypothesis H_priority_is_transitive: FP_is_transitive higher_eq_priority.
    
    (* Next, assume that the schedule is a work-conserving FP schedule. *)
    Hypothesis H_work_conserving: work_conserving job_cost sched.
    Hypothesis H_enforces_fp_policy: enforces_FP_policy job_cost job_task sched higher_eq_priority.
    
    (* Now we proceed with the analysis.
       Let tsk be any task in ts that is to be analyzed. *)
    Variable tsk: SporadicTask.
    Hypothesis H_tsk_in_ts: tsk \in ts.

    (* Recall the definition of response-time bound and the total workload bound W
       for tasks with higher-or-equal priority (with respect to tsk). *)
    Let response_time_bounded_by :=
      is_response_time_bound_of_task job_cost job_task sched.
    Let W := total_workload_bound_fp task_cost task_period higher_eq_priority ts tsk.

    (* Let R be any positive fixed point of the response-time recurrence. *)
    Variable R: time.
    Hypothesis H_R_positive: R > 0.
    Hypothesis H_response_time_is_fixed_point: R = W R.

    (* Since R = W R bounds the workload of higher-or-equal priority
       in any interval of length R, it follows from the busy-interval
       lemmas that R bounds the response-time of job j.
       (For more details, see model/uni/basic/busy_interval.v and
        analysis/uni/basic/workload_bound_fp.v.) *)
    Theorem uniprocessor_response_time_bound_fp:
      response_time_bounded_by tsk R.
    Proof.
      intros j JOBtsk.
      apply busy_interval_bounds_response_time with
        (job_task0 := job_task) (tsk0 := tsk)
        (higher_eq_priority0 := higher_eq_priority); try (by done).
      apply fp_workload_bound_holds with (task_cost0 := task_cost)
        (task_period0 := task_period) (task_deadline0 := task_deadline)
        (job_deadline0 := job_deadline) (ts0 := ts); try (by done).
    Qed.

  End ResponseTimeBound.

End ResponseTimeAnalysisFP.