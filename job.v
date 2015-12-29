Require Import task util_lemmas ssrnat ssrbool eqtype.  

Module Job.

  Section ValidJob.

    Context {Job: eqType}.
    Variable job_cost: Job -> nat.

    Variable j: Job.

    Definition job_cost_positive (j: Job) := job_cost j > 0.

  End ValidJob.

  Section ValidRealtimeJob.

    Context {Job: eqType}.
    Variable job_cost: Job -> nat.
    Variable job_deadline: Job -> nat.
    
    Variable j: Job.

    Definition job_cost_le_deadline := job_cost j <= job_deadline j.
    Definition job_deadline_positive := job_deadline j > 0.
        
    Definition valid_realtime_job :=
      job_cost_positive job_cost j /\
      job_cost_le_deadline /\
      job_deadline_positive.

  End ValidRealtimeJob.

  Section ValidSporadicTaskJob.

    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> nat.
    Variable task_deadline: sporadic_task -> nat.
    
    Context {Job: eqType}.
    Variable job_cost: Job -> nat.
    Variable job_deadline: Job -> nat.
    Variable job_task: Job -> sporadic_task.
    
    Variable j: Job.

    Definition job_cost_le_task_cost :=
      job_cost j <= task_cost (job_task j).
    Definition job_deadline_eq_task_deadline :=
      job_deadline j = task_deadline (job_task j).

    Definition valid_sporadic_job :=
      valid_realtime_job job_cost job_deadline j /\
      job_cost_le_task_cost /\
      job_deadline_eq_task_deadline.

  End ValidSporadicTaskJob.

  Section ValidSporadicTaskJobWithJitter.

    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> nat.
    Variable task_deadline: sporadic_task -> nat.
    Variable task_jitter: sporadic_task -> nat.
    
    Context {Job: eqType}.
    Variable job_cost: Job -> nat.
    Variable job_deadline: Job -> nat.
    Variable job_task: Job -> sporadic_task.
    Variable job_jitter: Job -> nat.
    
    Variable j: Job.

    Definition job_jitter_leq_task_jitter :=
      job_jitter j <= task_jitter (job_task j).

    Let j_is_valid_job :=
      valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j.

    Definition valid_sporadic_job_with_jitter :=
      j_is_valid_job /\ job_jitter_leq_task_jitter.

  End ValidSporadicTaskJobWithJitter.

End Job.