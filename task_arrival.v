Require Import Classical Vbase task job schedule helper
               ssreflect ssrbool eqtype ssrnat seq fintype bigop.

(* Whether the arrival sequence of a schedule is induced by a task set *)
Definition ts_arrival_sequence (ts: taskset) (sched: schedule) :=
  forall j t (ARR: arrives_at sched j t), (job_task j) \in ts.

(* The list of jobs that arrived before t' is obtained by concatenation *)
Definition prev_arrivals (sched: schedule) (t': time) : seq job :=
  \cat_(0 <= t < t') (arr_list sched t).

Lemma ts_finite_arrival_sequence :
  forall sched t' j, j \in prev_arrivals sched t' = arrived_before sched j t'.
Proof.
  unfold ts_arrival_sequence, prev_arrivals, arrived_before; ins.
  induction t'.
  {
    rewrite big_geq // in_nil.
    symmetry; apply/exists_inP_nat; unfold not; ins; des; intuition.
  }
  {
    rewrite big_nat_recr // mem_cat IHt'.
    destruct ([exists t_0 in 'I_t', arrives_at sched j t_0] || (j \in (arr_list sched) t')) eqn:OR.
    {
      move: OR => /orP OR; des.
      {
        rewrite OR orTb; symmetry; apply/exists_inP_nat.
        move: OR => /exists_inP_nat OR; des.
        exists x; split; [by apply (ltn_trans OR); ins | by ins].
      }
      {
        rewrite OR orbT; symmetry; apply/exists_inP_nat.
        exists t'; split; [by apply ltnSn | by ins].
      }
    }
    {
      rewrite OR; symmetry.
      apply negbT in OR; rewrite negb_or in OR.
      move: OR => /andP OR; des.
      rewrite negb_exists_in in OR.
      move: OR => /(forall_inP_nat t' (fun x => ~~ arrives_at sched j x)) OR.
      apply negbTE; rewrite negb_exists_in.
      apply/(forall_inP_nat t'.+1 (fun x => ~~ arrives_at sched j x)); ins.
      rewrite ltnS in LT; unfold arrives_at in *.
      move: LT; rewrite leq_eqVlt; move => /orP LT; des.
        by move: LT => /eqP LT; subst.
        by apply OR.
    }
  }
Qed.

Definition interarrival_times (sched: schedule) :=
  forall j arr (ARR: arrives_at sched j arr)
         j' (NEQ: j <> j') arr' (LE: arr <= arr')
         (EQtsk: job_task j' = job_task j)
         (ARR': arrives_at sched j' arr'),
    arr' >= arr + task_period (job_task j).

Definition periodic_task_model (ts: taskset) (sched: schedule) :=
  << ARRts: ts_arrival_sequence ts sched >> /\
  << INTER: interarrival_times sched >> /\
  << NEXT:
    forall j arr (ARRj: arrives_at sched j arr),
      exists j' arr',
        arr' = arr + task_period (job_task j) /\
        arrives_at sched j' arr' >>.

Definition sporadic_task_model (ts: taskset) (sched: schedule) :=
  << ARRts: ts_arrival_sequence ts sched >> /\
  << INTER: interarrival_times sched >> /\
  << NEXT:
    forall j arr (ARRj: arrives_at sched j arr),
      exists j' arr',
        arr' >= arr + task_period (job_task j) /\
        arrives_at sched j' arr' >>.

(* Synchronous release at time t *)
Definition sync_release (ts: taskset) (sched: schedule) (t: time) :=
  << ARRts: ts_arrival_sequence ts sched >> /\
  forall (tsk: sporadic_task) (IN: tsk \in ts),
    exists (j: job), job_task j = tsk /\ arrives_at sched j t.

Lemma uniq_prev_arrivals :
  forall sched t, uniq (prev_arrivals sched t).
Proof.
  ins; have arrProp := arr_properties (arr_list sched); des.
  have PROP := ts_finite_arrival_sequence sched t.
  (*
  assert (forall x, x \in (prev_arrivals sched t) -> (exists t0, t0 < t /\ x \in (arr_list sched t0))). admit.
  induction prev_arrivals; first by ins.
  rewrite cons_uniq; apply/andP; split.
    admit.
  {
    apply IHl; ins.
    specialize (H j).
    rewrite in_cons in H. rewrite H orbT in H.
    by exploit H.
  }*)
Admitted.