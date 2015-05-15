Require Import task.

Section Job.

Record job_data : Type :=
  {
    job_id: nat; (* job_id allows multiple jobs with same parameters *)
    job_cost: nat;
    job_deadline: nat; (* relative deadline *)
    job_of: option sporadic_task (* Whether a job is spawned by a particular task *)
  }.

(* A job represents a single execution unit. *)
Record job : Type :=
  { jd:> job_data;

    (* Properties of a job *)
    job_cost_positive: job_cost jd > 0;
    job_cost_le_deadline: job_cost jd <= job_deadline jd;
    job_deadline_positive: job_deadline jd > 0;
    job_task_parameters : forall (tsk: sporadic_task),
                              job_of jd = Some tsk ->
                                  (job_cost jd <= task_cost tsk
                                  /\ job_deadline jd = task_deadline tsk)
  }.

End Job.
