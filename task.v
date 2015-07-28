Require Import Vbase Bool.Sumbool
               eqtype ssrbool ssrnat fintype seq.

Section Task.

(* Sporadic Task Model *)
Record sporadic_task : Type :=
{
  task_id: nat; (* allows multiple tasks with same parameters *)
  task_cost: nat; (* worst-case cost *)
  task_period : nat; (* inter-arrival time *)
  task_deadline: nat; (* relative deadline *)

  (* Properties of a task *)
  task_properties: << task_cost_positive: task_cost > 0 >> /\
                   << task_period_positive: task_period > 0 >> /\
                   << task_deadline_positive: task_deadline > 0 >> /\
                   << task_cost_le_deadline: task_cost <= task_deadline >>
}.

(* Define decidable equality for tasks, so that it can be
   used in computations. *)
Definition task_eq_dec (x y: sporadic_task) : {x = y} + {x <> y}.
Admitted. (* This is VERY SLOW! *)
  (*  destruct x, y.
  destruct (eq_op task_id0 task_id1) eqn:Eid;
  destruct (eq_op task_cost0 task_cost1) eqn:Ecost;
  destruct (eq_op task_period0 task_period1) eqn:Eperiod;
  destruct (eq_op task_deadline0 task_deadline1) eqn:Edl;
  move: Eid Ecost Eperiod Edl => /eqP Eid /eqP Ecost /eqP Eperiod /eqP Edl; subst;
  try (by left; apply f_equal, proof_irrelevance);
  try (by right; unfold not; intro EQ; inversion EQ; intuition).
Defined.*)
Definition beq_task (x y: sporadic_task) := if task_eq_dec x y then true else false.

(* - ssreflect decidable equality -- IGNORE! - *)
  Lemma eqn_task : Equality.axiom beq_task.
  Proof.
    unfold beq_task, Equality.axiom; ins; desf;
    [by apply ReflectT | by apply ReflectF].  
  Qed.

  Canonical task_eqMixin := EqMixin eqn_task.
  Canonical task_eqType := Eval hnf in EqType sporadic_task task_eqMixin.
(* ----------------------------------------- *)

Definition taskset := seq sporadic_task.

(* Models for task deadlines *)
Definition implicit_deadline_model (ts: taskset) :=
  forall tsk (IN: tsk \in ts), task_deadline tsk = task_period tsk.

Definition restricted_deadline_model (ts: taskset) :=
  forall tsk (IN: tsk \in ts), task_deadline tsk <= task_period tsk.

Definition arbitrary_deadline_model (ts: taskset) := True.

End Task.