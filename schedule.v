Require Import List Arith.Gt Vbase task job helper.

(* Integer time *)
Definition time := nat.

(* Set of all possible job arrival sequences *)
Record arrival_sequence : Type :=
{
  arr :> job -> time -> Prop;
  no_multiple_arrivals: forall j t1 t2, arr j t1 -> arr j t2 -> t1 = t2
}.

Record schedule_data : Type :=
{
  (* service provided to a job at time t *)
  service_at: job -> time -> nat; 
  (* arrival sequence of the schedule *)
  arrives_at: arrival_sequence
}.

(* Service received by a job in a schedule, up to time t (inclusive) *)
Fixpoint service (sched: schedule_data) (j: job) (t: time) : nat :=
  match t with
      | 0 => service_at sched j 0
      | S t => service sched j t + service_at sched j (S t)
  end.

(* Whether a job arrived at time t *)
Definition arrived (sched: schedule_data) (j: job)  (t: time) :=
  exists t_0, t_0 <= t /\ (arrives_at sched) j t_0.

(* Whether a job is scheduled at time t *)
Definition scheduled (sched: schedule_data) (j: job) (t: time) :=
  service_at sched j t <> 0.

(* Whether a job has completed at time t *)
Definition completed (sched: schedule_data) (j: job) (t: time) :=
  t <> 0 /\ service sched j (t-1) = job_cost j.

(* Whether a job is pending and not scheduled at time t *)
Definition backlogged (sched: schedule_data) (j: job) (t: time) :=
  ~scheduled sched j t /\ ~completed sched j t.

Record schedule : Type :=
{
  sd:> schedule_data;

  sched_properties:
  (* A job can only be scheduled if it arrived *)
  << task_must_arrive_to_exec: forall j t, scheduled sd j t -> arrived sd j t >> /\

  (* A job cannot execute anymore after it completed *)
  << comp_task_no_exec:
       forall j t t_comp (jComp: completed sd j t_comp) (tAfter: t >= t_comp), ~ scheduled sd j t >>
}.

Lemma backlogged_no_service : forall sched j t,
  backlogged sched j t -> service_at sched j t = 0.
Proof.
  unfold backlogged, scheduled; ins; des.
  destruct (service_at sched j t); eauto; intuition.
Qed.

Lemma no_completed_tasks_at_time_zero : forall sched j, completed sched j 0 -> False.
Proof.
  unfold completed; ins; des; eauto.
Qed.

Lemma not_arrived_no_service :
  forall (sched: schedule) j t0 t_a (jArr: arrives_at sched j t_a) (t0Before: t0 < t_a),
    service sched j t0 = 0.
Proof.
  ins; des.
  assert (schedProp := sched_properties sched); des.
  clear comp_task_no_exec.
  unfold scheduled in task_must_arrive_to_exec.
  induction t0.
    simpl.
Admitted.