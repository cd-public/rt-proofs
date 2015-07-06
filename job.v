Require Import Vbase task.

Section Job.

Record job : Type :=
{
  (* UNNEEDED job_id: nat;*) (* job_id allows multiple jobs with same parameters *)
  job_arrival: nat; (* arrival time *)
  job_cost: nat; (* actual cost *)
  job_deadline: nat; (* absolute deadline *)
  job_task: sporadic_task; (* Task that spawns this job *)

  job_properties:
    (* UNNEEDED << job_cost_positive: job_cost > 0 >> /\ *)
    << job_cost_le_deadline: job_cost <= job_deadline >> /\
    (* UNNEEDED << job_dl_positive: job_deadline > 0 >> /\*)
    << job_params: (job_cost <= task_cost job_task /\
                    job_deadline = job_arrival + task_deadline job_task)>>
}.

(* Observations / TODO *)
(* 1) It should be ok to have 0-cost jobs. Deadlines can also be 0,
      as long as the cost is no greater than the deadline.

   2) job_task could be (option sporadic_task), so that we allow jobs that
      don't belong to any task. But our definition of job is not modular yet,
      so we could leave that for when we support different task models.
      to support more task models. We might require job_id as well, so that
      we allow multiple jobs of same arrival time.
*)

End Job.