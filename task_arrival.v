Require Import Classical Vbase task job schedule helper
               ssreflect ssrbool eqtype ssrnat seq fintype bigop.

(* Whether the arrival sequence of a schedule is induced by a task set *)
Definition ts_arrival_sequence (ts: taskset) (sched: schedule) :=
  forall j t (ARR: arrives_at sched j t), (job_task j) \in ts.

Definition task_job_unique (sched: schedule) :=
  forall t j1 j2 (EQtsk: job_task j1 = job_task j2)
         (ARR1: arrives_at sched j1 t) (ARR2: arrives_at sched j2 t), j1 = j2.

(* The list of jobs that arrived before t' is obtained by concatenation *)
Definition prev_arrivals (sched: schedule) (t': time) : seq job :=
  \cat_(0 <= t < t') (arr_list sched t).

Lemma ts_finite_arrival_sequence:
  forall ts sched (ARRts: ts_arrival_sequence ts sched) t' j,
    j \in prev_arrivals sched t' <-> arrived_before sched j t'.
Proof.
  unfold ts_arrival_sequence, prev_arrivals, arrived_before; ins.
  induction t'.
    rewrite big_geq // in_nil.
    by split; [|move/exists_inP_nat => EX]; ins; des; eauto.
  {
    rewrite big_nat_recr //; simpl in *.
    split; rewrite mem_cat.
    {
      move/orP => OR.
      destruct OR; [| by apply/exists_inP_nat; exists t'; rewrite leqnn].
        move: H => /IHt' /exists_inP_nat H; des.
        apply/exists_inP_nat; exists x; split; [|by ins].
        by apply ltn_trans with (n := t'); ins.
    }
    {
      move/exists_inP_nat => EX; des.
      rewrite leq_eqVlt eqSS in EX.
      apply/orP; move: EX => /orP EX.
      des; [by move: EX => /eqP EX; subst; right|].
      left; apply IHt'0; apply /exists_inP_nat.
      by unfold arrives_at in *; exists x; split; ins.
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