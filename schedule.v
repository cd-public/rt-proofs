Require Import Classical Vbase task job helper
               ssreflect ssrbool eqtype ssrnat seq fintype bigop.

(* Integer time *)
Definition time := nat.

(* Valid job arrival sequence *)
Record arrival_sequence : Type :=
{
  arr :> time -> seq job;
  arr_properties:
    << NOMULT: forall j t1 t2 (INj1: j \in (arr t1)) (INj2: j \in (arr t2)), t1 = t2 >> /\
    << ARR_PARAMS: forall j t (INj: j \in (arr t)), job_arrival j = t >>
}.

(* 1) This definition of arrival sequence allows retrieving the finite set of
      jobs that arrive at time t. So we can define things like the "Cumulative
      execution time of task T_5 during [3, 8)".
   2) Although it is a bit redundant to have the job arrival time both in the job
      and in the arrival sequence, it has some advantages. In case of the job,
      this allows retrieving the arrival time if we want to sort a sequence of jobs,
      for example. For the arrival sequence, it makes it easy to return a prefix.
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

Definition arrived_between (sched: schedule_data) (j: job) (t1 t2: nat) :=
  [exists t in 'I_(t2), ((t1 <= t) && arrives_at sched j t)].

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
       forall j t t_comp (jComp: completed sd j t_comp) (tAfter: t >= t_comp), ~~scheduled sd j t >>
}.

(* A carried-in job in [t1,t2) arrives before t1 and is not completed at time t1 *)
Definition carried_in (sched: schedule) (t1: time) (j: job) :=
  arrived_before sched j t1 && ~~ completed sched j t1.

(* A carried-out job in [t1,t2) arrives after t1 and is not completed at time t2 *)
Definition carried_out (sched: schedule) (t1 t2: time) (j: job) :=
  arrived_between sched j t1 t2 && ~~ completed sched j t2.

Lemma service_max_cost :
  forall (sched: schedule) j t
         (MAX: forall j t, service_at sched j t <= 1),
    service sched j t <= job_cost j.
Proof.
  unfold service; ins.
  have PROP := sched_properties sched; des; clear task_must_arrive_to_exec.
  unfold completed, scheduled in *.
  induction t; [by rewrite big_geq //|].
    rewrite big_nat_recr //.
    destruct (service sched j t == job_cost j) eqn:EQ.
    {
      apply comp_task_no_exec with (t := t) in EQ; [| by apply leqnn].
      rewrite negbK in EQ; move: EQ => /eqP EQ.
      by rewrite EQ /= addn0.
    }
    {
      unfold service in *.
      have LT: (\sum_(0 <= t_0 < t) service_at sched j t_0 < job_cost j).
        by rewrite ltn_neqAle; apply/andP; split; [by apply negbT|by ins].
      rewrite -[job_cost j] (ltn_predK LT) -addn1.
      apply leq_add; [|by apply MAX].
      by rewrite -ltnS (ltn_predK LT).
    }
Qed.

Lemma service_interval_max_cost :
  forall (sched: schedule) j t t'
         (MAX: forall j t, service_at sched j t <= 1),
    service_during sched j t t' <= job_cost j.
Proof.
  unfold service_during; ins.
  destruct (t > t') eqn:GT.
    by rewrite big_geq // -ltnS; apply ltn_trans with (n := t); ins.
    apply leq_trans with
      (n := \sum_(0 <= t0 < t') service_at sched j t0);
      [| by apply service_max_cost].
    rewrite -> big_cat_nat with (m := 0) (n := t);
      [by apply leq_addl | by ins | by rewrite leqNgt negbT //].
Qed.   

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
  have schedProp := sched_properties sched;
  have arrProp := arr_properties (arr_list sched); des; clear comp_task_no_exec.
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
        assert (t_a = x); eauto using NOMULT; subst.
        assert (x < t_0.+1); [by apply ltn_ord|]. exfalso.
        assert (x < x).
        apply ltn_trans with (n := t_0.+1); ins.
        rewrite ltnn in H0; eauto. 
      }
      by unfold scheduled in *; apply negbFE in SCHED; rewrite (eqP SCHED).
    }
    apply leq_ltn_trans with (n := t_0.+1); [by apply leqnSn | by ins].
Qed.

Lemma service_before_arrival :
  forall (sched: schedule) j t0 (LT: t0 < job_arrival j),
    service_at sched j t0 = 0.
Proof.
  ins; have arrPROP := arr_properties (arr_list sched); des.
  have schedPROP := sched_properties sched; des.
  rename task_must_arrive_to_exec into EXEC; specialize (EXEC j t0).
  apply contra with (c := scheduled sched j t0) (b := arrived sched j t0) in EXEC;
    first by rewrite -/scheduled negbK in EXEC; apply/eqP.
  {
    destruct (classic (exists arr_j, arrives_at sched j arr_j)) as [ARRIVAL|NOARRIVAL]; des;
    last by apply/negP; move => /exists_inP_nat ARRIVED; des; apply NOARRIVAL; exists x.
    {
      generalize ARRIVAL; apply ARR_PARAMS in ARRIVAL; ins.
      rewrite -> ARRIVAL in *.
      apply/negP; unfold not, arrived; move => /exists_inP_nat ARRIVED; des.
      apply leq_trans with (p := arr_j) in ARRIVED; last by ins.
      apply NOMULT with (t1 := x) in ARRIVAL0; last by ins.
      by subst; rewrite ltnn in ARRIVED.
    }
  }
Qed.

Lemma sum_service_before_arrival :
  forall (sched: schedule) j t0 (LT: t0 <= job_arrival j) m,
    \sum_(m <= i < t0) service_at sched j i = 0.
Proof.
  ins; apply/eqP; rewrite -leqn0.
  apply leq_trans with (n := \sum_(m <= i < t0) 0);
    last by rewrite big_const_nat iter_addn mul0n addn0.
  rewrite big_nat_cond [\sum_(_ <= _ < _) 0]big_nat_cond.
  apply leq_sum; intro i; rewrite andbT; move => /andP LTi; des.
  rewrite service_before_arrival; first by ins.
  by apply leq_trans with (n := t0); ins.
Qed.