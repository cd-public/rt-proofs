Require Import Vbase.

Module SporadicTask.

Parameter sporadic_task: Set.

Parameter task_cost: sporadic_task -> nat. (* worst-case cost *)
Parameter task_period: sporadic_task -> nat. (* inter-arrival time *)
Parameter task_deadline: sporadic_task -> nat. (* relative deadline *)

Definition valid_sporadic_task (tsk: sporadic_task) :=
  << task_cost_positive: task_cost tsk > 0 >> /\
  << task_period_positive: task_period tsk > 0 >> /\
  << task_deadline_positive: task_deadline tsk > 0 >> /\
  << task_cost_le_deadline: task_cost tsk <= task_deadline tsk >> /\
  << task_cost_le_period: task_cost tsk <= task_period tsk >>.

(* Assume decidable equality for computations using tasks. *)
Load eqtask_dec.

End SporadicTask.

Module SporadicTaskset.

Require Import ssrbool fintype seq.  
Export SporadicTask.
  
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

(*task_id: nat; (* allows multiple tasks with same parameters *) *)