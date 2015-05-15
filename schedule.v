Require Import job.
Require Import task.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Gt.
Require Import helper.

(* Integer time *)
Definition time := nat.

(* Set of all possible job arrival sequences *)
Record arrival_sequence : Type :=
  {
    arr :> job -> time -> Prop;
    no_multiple_arrivals: forall (j: job) (t1: time) (t2: time),
                              arr j t1 -> arr j t2 -> t1 = t2
  }.
(*Definition arrival_sequence := job -> time -> Prop.*)

Record schedule_data : Type :=
  {
    (* service provided to a job at time t *)
    service_at: job -> time -> nat; 
    (* arrival sequence of the schedule *)
    arrives_at: arrival_sequence
  }.

(* Service received by a job in a schedule, up to time t (inclusive) *)
Fixpoint service (sched: schedule_data) (j: job) (t: time) : nat:=
  match t with
      | 0 => service_at sched j 0
      | S t => service sched j t + service_at sched j (S t)
  end.

(* Whether a job arrived at time t *)
Definition arrived (sched: schedule_data) (j: job)  (t: time) : Prop :=
    exists (t_0: time), t_0 <= t /\ (arrives_at sched) j t_0.

(* Whether a job is scheduled at time t *)
Definition scheduled (sched: schedule_data) (j: job) (t: time) : Prop :=
    service_at sched j t > 0.

(* Whether a job has completed at time t *)
Definition completed (sched: schedule_data) (j: job) (t: time) : Prop :=
    t > 0 /\ service sched j (t-1) = job_cost j.

(* Whether a job is pending and not scheduled at time t *)
Definition backlogged (sched: schedule_data) (j: job) (t: time) : Prop :=
    ~scheduled sched j t /\ ~completed sched j t.

Record schedule : Type :=
  {
    sd:> schedule_data;

    (* Additional properties that a schedule must satisfy *)

    (* 1) A job can only be scheduled if it arrived *)
    task_must_arrive_to_exec :
        forall (j: job) (t: time),
            scheduled sd j t -> arrived sd j t;

    (* 2) A job cannot execute anymore after it completed *)
    completed_task_does_not_exec :
        forall (j: job) (t_comp: time),
            completed sd j t_comp ->
                forall (t: time), t >= t_comp -> ~ scheduled sd j t
  }.

Lemma backlogged_no_service : forall (sched: schedule) (j: job) (t: time),
    backlogged sched j t -> service_at sched j t = 0.
Proof.
    intros sched j t j_backlogged.
    unfold backlogged in j_backlogged.
    inversion j_backlogged as [not_scheduled _].
    unfold scheduled in not_scheduled.
    assert (H := gt_0_eq (service_at sched j t)).
    inversion H as [case1 | case2].
        contradiction.
        rewrite case2. reflexivity.
Qed.

Lemma no_completed_tasks_at_time_zero : forall (sched: schedule) (j: job) , ~completed sched j 0.
Proof.
    unfold not. intros.
    inversion H. inversion H0.
Qed.

Lemma not_arrived_no_service :
    forall (sched: schedule) (j: job) (t_a: time),
        arrives_at sched j t_a ->
        forall (t_0: time),
            t_0 < t_a -> service sched j t_0 = 0.
Proof.
    intros sched j t_a arr_j.
    assert (j_must_arrive := task_must_arrive_to_exec sched j).
    unfold scheduled in j_must_arrive.
    induction t_0.
      - intros t_a_positive.
        simpl.
        specialize (j_must_arrive 0).
        apply contrapositive in j_must_arrive.
        apply not_gt_le in j_must_arrive.
        inversion j_must_arrive. auto. 
        unfold not. intros j_arrives_at_0.
        assert (single_arrival := no_multiple_arrivals (arrives_at sched) j t_a 0 arr_j).
        inversion_clear j_arrives_at_0 as [t' [t'_zero j_arrives_at_t']].
        inversion t'_zero. subst t'. clear t'_zero.
        apply single_arrival in j_arrives_at_t'. subst t_a.
        inversion t_a_positive.

      (* TODO: simplify proof *)
      - intros S_t_0_less. simpl.
        assert (t_0_less : t_0 < t_a). omega.
        specialize (IHt_0 t_0_less).
        rewrite IHt_0. simpl.
        specialize (j_must_arrive (S t_0)).
        apply contrapositive in j_must_arrive.
        apply not_gt_le in j_must_arrive.
        inversion j_must_arrive. auto.
        assert (single_arrival := no_multiple_arrivals (arrives_at sched) j t_a (S t_0) arr_j).
        unfold not. intros j_arrives_at_St0.
        inversion_clear j_arrives_at_St0 as [t' [t'_zero j_arrives_at_t']].
        inversion t'_zero. subst t'. clear t'_zero.
        apply single_arrival in j_arrives_at_t'. subst t_a.
        omega. subst m.
        assert (H1 : t' < t_a). omega.
        assert (single_arrival2 := no_multiple_arrivals (arrives_at sched) j t_a t' arr_j j_arrives_at_t').
        omega.
Qed.
