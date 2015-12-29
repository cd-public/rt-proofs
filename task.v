Require Import Vbase util_lemmas ssrnat ssrbool eqtype fintype seq.

Module SporadicTask.
  (* Next we define valid parameters for a sporadic task*)
  Section BasicTask.
    Context {Task: eqType}.
    Variable task_cost: Task -> nat.
    Variable task_period: Task -> nat.
    Variable task_deadline: Task -> nat.

    Section ValidParameters.
      Variable tsk: Task.
    
      Definition task_cost_positive := task_cost tsk > 0.
      Definition task_period_positive := task_period tsk > 0.
      Definition task_deadline_positive := task_deadline tsk > 0.
      Definition task_cost_le_deadline := task_cost tsk <= task_deadline tsk.
      Definition task_cost_le_period := task_cost tsk <= task_period tsk.

      Definition is_valid_sporadic_task :=
        task_cost_positive /\ task_period_positive /\ task_deadline_positive /\
        task_cost_le_deadline /\ task_cost_le_period.

    End ValidParameters.
    
  End BasicTask.

End SporadicTask.

Module SporadicTaskset.
  Export SporadicTask.

  (* In this section we define a task set as a sequence of tasks. *)
  Section TasksetDefs.
 
    Definition taskset_of (T: eqType) := seq T.

    Section TasksetProperties.

      Context {Task: eqType}.
      Variable task_cost: Task -> nat.
      Variable task_period: Task -> nat.
      Variable task_deadline: Task -> nat.

      Let is_valid_task :=
        is_valid_sporadic_task task_cost task_period task_deadline.

      Variable ts: taskset_of Task.

      Definition valid_sporadic_taskset :=
        forall tsk,
          tsk \in ts -> is_valid_task tsk.

      (* Deadline models: implicit, restricted or arbitrary *)
      Definition implicit_deadline_model :=
        forall tsk,
          tsk \in ts -> task_deadline tsk = task_period tsk.

      Definition restricted_deadline_model :=
        forall tsk,
          tsk \in ts -> task_deadline tsk <= task_period tsk.

      Definition arbitrary_deadline_model := True.

    End TasksetProperties.

  End TasksetDefs.

End SporadicTaskset.