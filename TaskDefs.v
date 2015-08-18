Require Import Vbase.

Module Type SporadicTask.

Parameter sporadic_task: Set.

Parameter task_cost: sporadic_task -> nat. (* worst-case cost *)
Parameter task_period: sporadic_task -> nat. (* inter-arrival time *)
Parameter task_deadline: sporadic_task -> nat. (* relative deadline *)

(* Assume decidable equality for computations using tasks. *)
Load eqtask_dec.

End SporadicTask.



Module StructTask (SPO: SporadicTask) <: SporadicTask.
Require Import eqtype.
  
Record sporadic_task_rec :=
{
  task_cost: nat;
  task_period: nat;
  task_deadline: nat
}.

Definition sporadic_task := sporadic_task_rec.

Axiom task_eq_dec: sporadic_task -> sporadic_task -> bool.
Axiom eqn_task : Equality.axiom task_eq_dec.
Canonical task_eqMixin := EqMixin eqn_task.
Canonical task_eqType := Eval hnf in EqType sporadic_task task_eqMixin.

End StructTask.



Module ValidSporadicTask (TSK: SporadicTask).
Import TSK.

Section ValidTask.

Variable tsk: sporadic_task.
  
Definition task_cost_positive := task_cost tsk > 0.
Definition task_period_positive := task_period tsk > 0.
Definition task_deadline_positive := task_deadline tsk > 0.
Definition task_cost_le_deadline := task_cost tsk <= task_deadline tsk.
Definition task_cost_le_period := task_cost tsk <= task_period tsk.

Definition valid_sporadic_task :=
  task_cost_positive /\ task_period_positive /\ task_deadline_positive /\
  task_cost_le_deadline /\ task_cost_le_period.

End ValidTask.

End ValidSporadicTask.



Module SporadicTaskset.

Module SPO: SporadicTask.
Module ValidTask := ValidSporadicTask SPO.
Require Import ssrbool fintype seq.  
Export SPO ValidTask.
  
(* Define task set as a sequence of sporadic tasks. *)
Definition sporadic_taskset := seq sporadic_task.

Section TasksetProperties.

Variable ts: sporadic_taskset.

Definition valid_sporadic_taskset :=
  forall tsk (IN: tsk \in ts), valid_sporadic_task tsk.

(* Deadline models: implicit, restricted or arbitrary *)
Definition implicit_deadline_model :=
  forall tsk (IN: tsk \in ts), task_deadline tsk = task_period tsk.

Definition restricted_deadline_model :=
  forall tsk (IN: tsk \in ts), task_deadline tsk <= task_period tsk.

Definition arbitrary_deadline_model := True.

End TasksetProperties.

End SporadicTaskset.

