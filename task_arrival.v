Require Import Classical Vbase task job schedule
               ssreflect ssrbool eqtype ssrnat seq fintype bigop.

(* Whether the arrival sequence of a schedule is induced by a task set *)
Definition ts_arrival_sequence (ts: taskset) (sched: schedule) :=
  forall j t (ARR: arrives_at sched j t), (job_task j) \in ts.

Definition task_job_unique (sched: schedule) :=
  forall t j1 j2 (EQtsk: job_task j1 = job_task j2)
         (ARR1: arrives_at sched j1 t) (ARR2: arrives_at sched j2 t), j1 = j2.

Definition prev_arrivals (sched: schedule) (t': time) : seq job :=
  (\big[cat/nil]_(0 <= t < t') arr_list sched t).

Lemma ts_finite_arrival_sequence:
  forall ts sched (ARRts: ts_arrival_sequence ts sched)
         (UNIQUE: task_job_unique sched) t' j,
    j \in prev_arrivals sched t' <-> arrived_before sched j t'.
Proof.
  unfold ts_arrival_sequence, prev_arrivals, arrived_before; ins.
  induction t'.
  {
    rewrite big_geq // in_nil.
    split; [by ins|].
      move/exists_inP => EX; des.
      move: H1 => /enum_rank_subproof.
      by rewrite card_ord //.
  }
  {
    rewrite big_nat_recr //.
    split; rewrite mem_cat.
    {
      move/orP => OR.
      destruct OR.
        move: H => /IHt' /exists_inP H; des.
        apply/exists_inP; exists (inord x).
        apply predT_subset; by ins.
        by rewrite inordK // ltnS; eauto.
        apply/exists_inP; exists (inord t').
        apply predT_subset; by ins.
        by rewrite -/arrives_at inordK; eauto.
    }
    {
      move/exists_inP => EX; des.
      apply/orP.
      destruct (t' == x) eqn:EQ; [by move: EQ => /eqP EQ; right; rewrite EQ|].
      apply negbT in EQ; move: (ltn_ord x); rewrite ltnS => Le.
      have LT : x < t'.
        by rewrite ltn_neqAle; apply/andP; split; [rewrite eq_sym|].
      left; apply IHt'0.
      apply/exists_inP.
      exists (Ordinal LT); eauto.
    }
  }
Qed.
  
(* Sporadic arrival times for every task in a taskset.
   We use only '->' because the first arrival may be at any point. *)
Definition periodic_task_model (ts: taskset) (sched: schedule) :=
  << ARRts: ts_arrival_sequence ts sched >> /\
  << UNIQUE: task_job_unique sched >> /\ 
  << NEXT:
    forall j arr (ARRj: arrives_at sched j arr),
    exists j' arr', job_task j' = job_task j /\
                   arrives_at sched j' arr' /\
                   arr' = arr + task_period (job_task j) >>.

(* Periodic arrival times *)
Definition sporadic_task_model (ts: taskset) (sched: schedule) :=
  << ARRts: ts_arrival_sequence ts sched >> /\
  << UNIQUE: task_job_unique sched >> /\ 
  << NEXT:
    forall j arr (ARRj: arrives_at sched j arr),
    exists j' arr', job_task j' = job_task j /\
                    arrives_at sched j' arr' /\
                    arr' >= arr + task_period (job_task j) >>.

(* Synchronous release at time t *)
Definition sync_release (ts: taskset) (sched: schedule) (t: time) :=
  << ARRts: ts_arrival_sequence ts sched >> /\
  forall (tsk: sporadic_task) (IN: tsk \in ts),
    exists (j: job), job_task j = tsk /\ arrives_at sched j t.