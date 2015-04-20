Set Printing Projections.

Require Import Coq.Lists.List.

(* A task represents an execution requirement *)
Record job : Type :=
  { job_id: nat;
    job_cost: nat;
    job_deadline: nat
  }.

(* Restrictions on job parameters *)
Record valid_job (j: job) : Prop :=
  { job_cost_positive: job_cost j > 0;
    job_cost_le_deadline: job_cost j <= job_deadline j;
    job_deadline_positive: job_deadline j > 0
  }.

(* A sporadic task has an interarrival time *)
Record sporadic_task : Type :=
  { task_cost: nat;
    task_period : nat;
    task_deadline: nat
  }.

Definition taskset := list sporadic_task.

Axiom job_of : job -> sporadic_task -> Prop.

Definition task_parameters (j: job) (tsk: sporadic_task) : Prop :=
    job_of j tsk ->
        (job_cost j <= task_cost tsk /\
         job_deadline j = task_deadline tsk).