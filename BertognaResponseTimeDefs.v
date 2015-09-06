Require Import Vbase TaskDefs JobDefs TaskArrivalDefs ScheduleDefs
               PlatformDefs WorkloadDefs SchedulabilityDefs
               ResponseTimeDefs divround helper
               ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Module ResponseTimeAnalysis.

  Import SporadicTaskset Schedule Workload Schedulability ResponseTime.

  Section Interference.

    Variable ts: sporadic_taskset.
    Variable tsk: sporadic_task.

    Variable delta: time.
    
    (* Interference caused by tsk due to tsk_other *)
    Definition interference_incurred_by (tsk tsk_other: sporadic_task) :=
      delta.
          
    Definition total_interference :=
      \sum_(tsk_other <- ts)
         (interference_incurred_by tsk) tsk_other.

  End Interference.
  
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