Require Import Vbase task.

Section Job.

Record job : Type :=
{
  job_id: nat; (* job_id allows multiple jobs with same parameters *)
  job_cost: nat;
  job_deadline: nat; (* relative deadline *)
  job_of: option sporadic_task; (* Whether a job is spawned by a particular task *)

  job_properties:
    << job_cost_positive: job_cost > 0 >> /\
    << job_cost_le_deadline: job_cost <= job_deadline >> /\
    << job_dl_positive: job_deadline > 0 >> /\
    << job_params: forall tsk (jTsk: job_of = Some tsk),
                     (job_cost <= task_cost tsk /\
                      job_deadline = task_deadline tsk)>>
}.

End Job.
