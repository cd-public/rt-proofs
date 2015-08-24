Require Import Vbase helper ssrnat TaskDefs.  

Module Job.

  Definition job := (nat * nat) % type.

  (* Assume decidable equality for computations involving jobs. *)
  Load eqjob_dec.

  Section JobParameters.
    Definition job_arrival (j: job) := pair_1st j.
    Definition job_cost (j: job) := pair_2nd j.
  End JobParameters.

  Definition valid_job (j: job) := job_cost j > 0.
  
End Job.

Module RealtimeJob.
  Export Job.
  
  Definition realtime_job := (job * nat) % type.
  
  Section JobParameters.
    Coercion RTJob_is_Job (j: realtime_job) := pair_1st j.
    Definition job_deadline (j: realtime_job) := pair_2nd j.
  End JobParameters.

  Section ValidJob.
    Variable j: realtime_job.

    Definition job_cost_le_deadline := job_cost j <= job_deadline j.
    Definition job_dl_positive := job_deadline j > 0.
        
    Definition valid_realtime_job :=
      valid_job j /\ job_cost_le_deadline /\ job_dl_positive.
  End ValidJob.
  
End RealtimeJob.

Module SporadicTaskJob.
  Export SporadicTask.
  Export RealtimeJob.

  Definition sporadic_task_job := (realtime_job * sporadic_task) % type.

  Section JobParameters.
    Coercion SpoJob_is_RTJob (j: sporadic_task_job) := fst j.
    Definition job_task (j: sporadic_task_job) := snd j.
  End JobParameters.

  Section ValidJob.
    Variable j: sporadic_task_job.

    Definition job_cost_le_task_cost :=
      job_cost j <= task_cost (job_task j).
    Definition job_deadline_eq_task_deadline :=
      job_deadline j = task_deadline (job_task j).
    
    Definition valid_sporadic_task_job :=
      valid_realtime_job j /\
      job_cost_le_task_cost /\
      job_deadline_eq_task_deadline.
  End ValidJob.
  
End SporadicTaskJob.

(*Module SuspendingJob.
  Import SporadicTask.
  Export Job.

  Definition suspending_job := (job * (list (nat * nat))) % type.

  Section JobParameters.
    Coercion SuspJob_is_RTJob (j: suspending_job) := fst j.
    Definition job_suspensions (j: suspending_job) := snd j.
  End JobParameters.
End SuspendingJob.

Module SporadicSuspendingJob.
  Export SporadicTask.
  Export SporadicTaskJob.
  Export SuspendingJob.
  
  Definition sporadic_suspending_job :=
    (sporadic_task_job * suspending_job) % type.

  Section JobParameters.
    Coercion SpoSuspJob_is_SpoJob (j: sporadic_suspending_job) := fst j.
    Coercion SpoSuspJob_is_SusJob (j: sporadic_suspending_job) := snd j.
  End JobParameters.
End SporadicSuspendingJob.

Module Test.
  Import SporadicSuspendingJob.

  Variable j: sporadic_suspending_job.
  Variable j': sporadic_task_job.
  Check job_suspensions j.
  Check job_deadline j.
  Check job_task j.

  Definition time := nat.
  Definition service := job -> time -> nat.

  Variable serv: service.
  Check (serv j 5).
  Check (serv j' 10).*)