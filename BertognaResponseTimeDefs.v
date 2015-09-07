Require Import Vbase TaskDefs JobDefs TaskArrivalDefs ScheduleDefs
               PlatformDefs WorkloadDefs SchedulabilityDefs
               ResponseTimeDefs divround helper
               ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Module ResponseTimeAnalysis.

  Import SporadicTaskset Schedule Workload Schedulability ResponseTime.

  Section InterferenceBound.

    Variable ts: sporadic_taskset.
    Variable tsk: sporadic_task.

    (* Given a known response-time bound for each interfering task ... *)
    Variable R: sporadic_task -> time.
    (* ... and an interval length delta, ... *)
    Variable delta: time.

    Definition workload_bound (tsk_other: sporadic_task) :=
      W tsk_other (R tsk_other) delta.
    
    (* the interference incurred by tsk due to tsk_other is bounded by the
       workload of tsk_other. *)
    Definition interference_caused_by (tsk_other: sporadic_task) :=
      workload_bound tsk_other.

    (* Then, Bertogna and Cirinei define two interference bounds: one for FP and another
       for JLFP scheduling. *)
    Section InterferenceFP.

      (* Under FP scheduling, only the higher-priority tasks cause interference.
         The total interference incurred by tsk is bounded by: *)
      Definition total_interference_fp :=
        \sum_(tsk_other <- ts | true)
           interference_caused_by tsk_other.
  
    End InterferenceFP.

    Section InterferenceJLFP.

      (* Under JLFP scheduling, every task other than tsk can cause interference.
         The total interference incurred by tsk is bounded by: *)
      Definition total_interference_jlfp :=
        \sum_(tsk_other <- ts | tsk_other != tsk)
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

    (* Bertogna and Cirinei's response-time bound recurrence *)
    Definition response_time_recurrence R :=
      R <= task_cost tsk + div_floor
                             (total_interference ts tsk R)
                             num_cpus.

    Definition no_deadline_is_missed_by_tsk (tsk: sporadic_task) :=
      task_misses_no_deadline job_cost job_deadline job_task rate sched tsk.

    Definition response_time_bounded_by :=
      is_response_time_bound_of_task job_cost job_task tsk rate sched.
    
    Theorem bertogna_cirinei_response_time_bound :
      forall R,
        response_time_recurrence R ->
        R <= task_deadline tsk ->
        response_time_bounded_by R.
    Proof.
      Admitted.
    
  End ResponseTimeBound.
  
End ResponseTimeAnalysis.