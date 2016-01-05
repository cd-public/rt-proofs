Require Import Vbase util_lemmas ssrnat ssrbool eqtype fintype seq.

(* Attributes of a valid sporadic task. *)
Module SporadicTask.

  Section BasicTask.
    Context {Task: eqType}.
    Variable task_cost: Task -> nat.
    Variable task_period: Task -> nat.
    Variable task_deadline: Task -> nat.

    Section ValidParameters.
      Variable tsk: Task.

      (* The cost, period and deadline of the task must be positive. *)
      Definition task_cost_positive := task_cost tsk > 0.
      Definition task_period_positive := task_period tsk > 0.
      Definition task_deadline_positive := task_deadline tsk > 0.

      (* The task cost cannot be larger than the deadline or the period. *)
      Definition task_cost_le_deadline := task_cost tsk <= task_deadline tsk.
      Definition task_cost_le_period := task_cost tsk <= task_period tsk.

      Definition is_valid_sporadic_task :=
        task_cost_positive /\ task_period_positive /\ task_deadline_positive /\
        task_cost_le_deadline /\ task_cost_le_period.

    End ValidParameters.
    
  End BasicTask.

End SporadicTask.

(* Definition and properties of a task set. *)
Module SporadicTaskset.
  Export SporadicTask.

  Section TasksetDefs.

    (* A task set is just a sequence of tasks. *)
    Definition taskset_of (Task: eqType) := seq Task.

    (* Next, we define some properties of a task set. *)
    Section TasksetProperties.

      Context {Task: eqType}.
      Variable task_cost: Task -> nat.
      Variable task_period: Task -> nat.
      Variable task_deadline: Task -> nat.

      Let is_valid_task :=
        is_valid_sporadic_task task_cost task_period task_deadline.

      Variable ts: taskset_of Task.

      (* A valid sporadic taskset only contains valid tasks. *)
      Definition valid_sporadic_taskset :=
        forall tsk,
          tsk \in ts -> is_valid_task tsk.

      (* A task set can satisfy one of three deadline models:
         implicit, restricted, or arbitrary. *)
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