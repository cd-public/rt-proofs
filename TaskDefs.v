Require Import Vbase helper ssrnat.

Module SporadicTask.

  Definition sporadic_task := (nat * nat * nat) % type.

  Section TaskParameters.
    Variable tsk: sporadic_task.

    Definition task_cost := triple_1st tsk.
    Definition task_period := triple_2nd tsk.
    Definition task_deadline := triple_3rd tsk.
  End TaskParameters.

  (* Assume decidable equality for computations involving tasks. *)
  Load eqtask_dec.

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
