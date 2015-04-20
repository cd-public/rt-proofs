(* Restrictions on task parameters *)
Record valid_task (tsk: task) : Prop :=
  { job_cost_positive: job_cost tsk > 0;
    job_cost_le_deadline: job_cost tsk <= job_deadline tsk;
    job_deadline_positive: job_deadline tsk > 0
  }.

(* A sporadic task has an interarrival time *)
Record sporadic_task : Type :=
  { sporadic_task_is_task :> task;
    task_period : nat
  }.

(* Restrictions on sporadic task parameters *)
Record valid_sporadic_task (tsk: sporadic_task) : Prop :=
  { sporadic_task_valid: valid_task tsk;
    job_interarrival:
        forall t1 t2, (t1 <> t2
                      /\ job_arrival tsk t1
                      /\ job_arrival tsk t2)
                      -> t1 <= t2 + task_period tsk
  }.

Definition job_interarrival_fixed (tsk: sporadic_task) := forall t1 t2,
                      (t1 <> t2
                      /\ job_arrival tsk t1
                      /\ job_arrival tsk t2)
                      -> t1 <= t2 + task_period tsk.

Definition periodic_task := {tsk: sporadic_task | valid_sporadic_task tsk
                                                  /\ job_interarrival_fixed tsk }.