Set Printing Projections.

(* A task represents an execution requirement *)
Record task : Type :=
  { job_arrival: nat -> Prop;
    job_cost: nat;
    job_deadline: nat
  }.

(* Restrictions on task parameters *)
Record valid_task (tsk: task) : Prop :=
  { job_cost_positive: job_cost tsk > 0;
    job_cost_le_deadline: job_cost tsk <= job_deadline tsk;
    job_deadline_positive: job_deadline tsk > 0
  }.

(* A periodic task has an interarrival time *)
Record periodic_task : Type :=
  { periodic_task_is_task :> task;
    task_period : nat
  }.

(* Restrictions on periodic task parameters *)
Record valid_periodic_task (tsk: periodic_task) : Prop :=
  { periodic_task_valid: valid_task tsk;
    job_interarrival:
        forall t1 t2, t1 <> t2
                      /\ job_arrival tsk t1
                      /\ job_arrival tsk t2
                      -> t1 <= t2 + task_period tsk
  }.