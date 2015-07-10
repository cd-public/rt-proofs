Require Import List Classical Vbase task job schedule.

(* Whether the arrival sequence of a schedule is induced by a task set *)
Definition ts_arrival_sequence (ts: taskset) (sched: schedule) :=
  forall j t (ARR: arrives_at sched j t), In (job_task j) ts.

(* Since the number of tasks is finite, and each task does not
   spawn more than one job per time instant, the number of jobs
   released in a bounded interval is finite. *)
Definition arrival_list (sched: schedule) (l: list job) (t: time) :=
  forall j, << IN: In j l >> <->
            << ARRIVED: (arrived sched j t) >>.

(*Lemma released_jobs_at_time:
  forall ts sched t (ARRts: ts_arrival_sequence ts sched),
    exists (l: list job),
      forall j, In j l <-> arrives_at sched j t.
Proof.
  unfold ts_arrival_sequence; ins.
  (*cut (exists l, forall j, exists tsk, In j l <-> (arrives_at sched) j t /\ job_task j = tsk).
    by ins; des; exists l; ins; rewrite H with (tsk := job_task j) in *; split; ins; des.
    induction ts.
      by exists nil; split; ins; des; eauto.

    by rewrite H with (tsk := job_task j) in *; des.
      apply ARRts in H0.
  destruct ts. exists nil; split; ins; eauto.
  destruct (classic (exists j, arrives_at sched j t /\ job_task j = s)); des.
  admit.*)
  induction ts; ins.
    exists nil; split; ins; eauto.
    

    destruct (classic (exists j, arrives_at sched j t )); des.

      by eauto.
*)      
Lemma ts_finite_arrival_sequence:
  forall ts sched (ARRts: ts_arrival_sequence ts sched) (t: time),
    exists (l: list job), arrival_list sched l t.
Proof.
  unfold ts_arrival_sequence, arrival_list; ins.
  induction t.
  exists (map (arrives_at sched t))
  unfold arrived.
Admitted.

(* Sporadic arrival times for every task in a taskset.
   We use only '->' because the first arrival may be at any point. *)
Definition periodic_task_model (ts: taskset) (sched: schedule) :=
  << ARRts: ts_arrival_sequence ts sched >> /\
  forall j arr (ARRj: arrives_at sched j arr),
    exists (j': job) (arr': time), job_task j' = job_task j /\
                                   arrives_at sched j' arr' /\
                                   arr' = arr + task_period (job_task j).

(* Periodic arrival times *)
Definition sporadic_task_model (ts: taskset) (sched: schedule) :=
  << ARRts: ts_arrival_sequence ts sched >> /\
  forall j arr (ARRj: arrives_at sched j arr),
    exists (j': job) (arr': time), job_task j' = job_task j /\
                                   arrives_at sched j' arr' /\
                                   arr' >= arr + task_period (job_task j).

(* Synchronous release at time t *)
Definition sync_release (ts: taskset) (sched: schedule) (t: time) :=
  << ARRts: ts_arrival_sequence ts sched >> /\
  forall (tsk: sporadic_task) (IN: In tsk ts),
    exists (j: job), job_task j = tsk /\ arrives_at sched j t.