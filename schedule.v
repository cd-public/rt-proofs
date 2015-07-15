Require Import Classical Vbase task job helper
               ssreflect ssrbool eqtype ssrnat seq fintype bigop.

(* Integer time *)
Definition time := nat.

(* Set of all possible job arrival sequences *)
Record arrival_sequence : Type :=
{
  arr :> time -> seq job;
  no_multiple_arrivals: forall j t1 t2, j \in (arr t1) -> j \in (arr t2) -> t1 = t2
}.

(* 1) This definition of arrival sequence allows retrieving the finite set of
      jobs that arrive at time t. So we can define things like the "Cumulative
      execution time of task T_5 during [3, 8)".
*)

Record schedule_data : Type :=
{
  (* service received by a job during [t, t+1) *)
  service_at: job -> time -> nat;
  (* arrival sequence of the schedule *)
  arr_list: arrival_sequence
}.

Definition arrives_at (sched: schedule_data) (j: job) (t: time) :=  j \in arr_list sched t.

Definition service_during (sched: schedule_data) (j: job) (t1 t2: time) :=
  \sum_(t1 <= t < t2) (service_at sched j t).

(* Cumulative service received by a job in a schedule before time t, i.e., during [0, t) *)
Definition service (sched: schedule_data) (j: job) (t': time):=
  \sum_(0 <= t < t') (service_at sched j t).

(* Whether a job arrived at time t *)

(* A job has arrived at time t iff it arrives at some time t_0, with 0 <= t_0 < t+1. *)
Definition arrived (sched: schedule_data) (j: job) (t: nat) :=
  [exists t_0 in 'I_(t.+1), arrives_at sched j t_0].

Definition arrived_before (sched: schedule_data) (j: job) (t: nat) :=
  [exists t_0 in 'I_(t), arrives_at sched j t_0].

(* Whether a job is scheduled at time t *)
Definition scheduled (sched: schedule_data) (j: job) (t: time) :=
  service_at sched j t != 0.

(* Whether a job has completed at time t (assumes costs are non-zero!) *)
Definition completed (sched: schedule_data) (j: job) (t: time) :=
  service sched j t == job_cost j.

Definition pending (sched: schedule_data) (j: job) (t: time) :=
  arrived sched j t && ~~completed sched j t.

(* Whether a job is pending and not scheduled at time t *)
Definition backlogged (sched: schedule_data) (j: job) (t: time) :=
  pending sched j t && ~~scheduled sched j t.

Record schedule : Type :=
{
  sd:> schedule_data;

  sched_properties:
    (* A job can only be scheduled if it arrived *)
    << task_must_arrive_to_exec: forall j t, scheduled sd j t -> arrived sd j t >> /\

    (* A job cannot be scheduled after it completed *)
    << comp_task_no_exec:
       forall j t t_comp (jComp: completed sd j t_comp) (tAfter: t >= t_comp), ~ scheduled sd j t >>
}.

Definition earlier_job (sched: schedule) (j1 j2: job) :=
  << EQtsk: job_task j1 = job_task j2 >> /\
  exists arr1 arr2, << ARR1: arrives_at sched j1 arr1 >> /\
                    << ARR2: arrives_at sched j2 arr2 >> /\
                    << LT: arr1 < arr2 >>.
  
Lemma backlogged_no_service : forall sched j t,
  backlogged sched j t -> service_at sched j t = 0.
Proof.
  unfold backlogged, scheduled; ins; unfold negb in *; desf;
  destruct (service_at sched j t); intuition; exfalso; eauto.
Qed.

Lemma no_completed_tasks_at_time_zero : forall sched j, completed sched j 0 -> False.
Proof.
  unfold completed, service; ins; assert (PROPj := job_properties j); des.
  rewrite big_geq in H; [|by trivial].
  rewrite <- (eqP H) in *; ins.
Qed.

Lemma not_arrived_no_service :
  forall (sched: schedule) j t_a (jArr: arrives_at sched j t_a) t_0 (t0Before: t_0 < t_a),
    service sched j t_0 = 0.
Proof.
  unfold service; ins; des.
  assert (schedProp := sched_properties sched); des; clear comp_task_no_exec.
  induction t_0; [by rewrite big_geq|].
  (* Inductive step *)
    rewrite big_nat_recr; [|by trivial]; simpl.
    rewrite -> IHt_0, add0n.
    {
      destruct (scheduled sched j t_0) eqn:SCHED.
      {
        apply task_must_arrive_to_exec in SCHED.
        unfold arrived in SCHED.
        assert (EX := exists_inP SCHED); des.
        assert (t_a = x); eauto using no_multiple_arrivals; subst.
        assert (x < t_0.+1); [by apply ltn_ord|]. exfalso.
        assert (x < x).
        apply ltn_trans with (n := t_0.+1); ins.
        rewrite ltnn in H0; eauto. 
      }
      by unfold scheduled in *; apply negbFE in SCHED; rewrite (eqP SCHED).
    }
    apply leq_ltn_trans with (n := t_0.+1); [by apply leqnSn | by ins].
Qed.