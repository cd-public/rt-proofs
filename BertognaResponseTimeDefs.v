Require Import Vbase TaskDefs JobDefs TaskArrivalDefs ScheduleDefs
               PlatformDefs WorkloadDefs SchedulabilityDefs PriorityDefs
               ResponseTimeDefs divround helper
               ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Module ResponseTimeAnalysis.

  Import SporadicTaskset Schedule Workload Schedulability ResponseTime Priority.

  Section InterferenceBound.

    Variable ts: sporadic_taskset.
    Variable tsk: sporadic_task.

    (* Given a known response-time bound for each interfering task ... *)
    Variable R_other: sporadic_task -> time.
    (* ... and an interval length delta, ... *)
    Variable delta: time.

    Definition workload_bound (tsk_other: sporadic_task) :=
      W tsk_other (R_other tsk_other) delta.
    
    (* the interference incurred by tsk due to tsk_other is bounded by the
       workload of tsk_other. *)
    Definition interference_caused_by (tsk_other: sporadic_task) :=
      if tsk_other != tsk then
        workload_bound tsk_other
      else 0.
    
    (* Then, Bertogna and Cirinei define two interference bounds: one for FP and another
       for JLFP scheduling. *)
    Section InterferenceFP.

      Variable higher_eq_priority: fp_policy.

      Definition is_interfering_task :=
        fun tsk_other => higher_eq_priority tsk_other tsk.
      
      (* Under FP scheduling, only the higher-priority tasks cause interference.
         The total interference incurred by tsk is bounded by: *)
      Definition total_interference_fp :=
        \sum_(tsk_other <- ts | is_interfering_task tsk_other)
           interference_caused_by tsk_other.
  
    End InterferenceFP.

    Section InterferenceJLFP.
      
      (* Under JLFP scheduling, every task other than tsk can cause interference.
         The total interference incurred by tsk is bounded by: *)
      Definition total_interference_jlfp :=
        \sum_(tsk_other <- ts)
           interference_caused_by tsk_other.

    End InterferenceJLFP.

  End InterferenceBound.
  
  Section ResponseTimeBound.
    
    Context {Job: eqType}.
    Variable job_cost: Job -> nat.
    Variable job_deadline: Job -> nat.
    Variable job_task: Job -> sporadic_task.
    
    Context {arr_seq: arrival_sequence Job}.
  
    Variable num_cpus: nat.
    Variable rate: Job -> processor num_cpus -> nat.
    Variable sched: schedule num_cpus arr_seq.

    Variable ts: sporadic_taskset.
    Variable tsk: sporadic_task.
    Hypothesis task_in_ts: tsk \in ts.

    Definition no_deadline_is_missed_by_tsk (tsk: sporadic_task) :=
      task_misses_no_deadline job_cost job_deadline job_task rate sched tsk.

    Definition is_response_time_bound (tsk: sporadic_task) :=
      is_response_time_bound_of_task job_cost job_task tsk rate sched.
    
    Variable R_other: sporadic_task -> time.

    Section UnderFPScheduling.

      Variable higher_eq_priority: fp_policy.

      Hypothesis response_time_of_interfering_tasks_is_known:
        forall tsk_other,
          tsk_other \in ts -> (* --> ugly, convert this to some predicate *)
          tsk_other != tsk ->
          higher_eq_priority tsk_other tsk ->
          is_response_time_bound tsk_other (R_other tsk_other).

      (* Bertogna and Cirinei's response-time bound recurrence *)
      Definition response_time_recurrence_fp R :=
        R <= task_cost tsk + div_floor
                               (total_interference_fp ts tsk R_other R higher_eq_priority)
                               num_cpus.

      Variable R: time.

      Hypothesis response_time_recurrence_holds:
        response_time_recurrence_fp R.

      Hypothesis response_time_no_larger_than_deadline:
        R <= task_deadline tsk.
      
      Theorem bertogna_cirinei_response_time_bound_fp :
        is_response_time_bound tsk R.
      Proof.
        unfold response_time_recurrence_fp; ins.      
      Admitted.

    End UnderFPScheduling.

    Section UnderJLFPScheduling.

      (* Bertogna and Cirinei's response-time bound recurrence *)
      Definition response_time_recurrence_jlfp R :=
        R <= task_cost tsk + div_floor
                             (total_interference_jlfp ts tsk R_other R)
                             num_cpus.

      Variable R: time.

      Hypothesis response_time_recurrence_holds:
        response_time_recurrence_jlfp R.

      Hypothesis response_time_no_larger_than_deadline:
        R <= task_deadline tsk.

      Theorem bertogna_cirinei_response_time_bound_jlfp :
        is_response_time_bound tsk R.
      Proof.
      Admitted.
      
    End UnderJLFPScheduling.
    
  End ResponseTimeBound.
  
End ResponseTimeAnalysis.