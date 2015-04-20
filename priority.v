Add LoadPath "/home/felipec/dev/coq/rt-scheduling-spec".
Require Import job.
Require Import schedule.

Definition fp_order := sporadic_task -> sporadic_task -> Prop.

Definition RM (tsk1: sporadic_task) (tsk2: sporadic_task) : Prop :=
    task_period tsk1 < task_period tsk2.

Definition DM (tsk1: sporadic_task) (tsk2: sporadic_task) : Prop :=
    task_deadline tsk1 < task_deadline tsk2.

Axiom task_id : sporadic_task -> nat.
Definition fp_higherprio (order: fp_order) (tsk1: sporadic_task) (tsk2: sporadic_task) : Prop :=
    order tsk1 tsk2 \/ task_id tsk1 < task_id tsk2.

Definition fixed_priority (hp: higher_priority) (order: fp_order) : Prop :=
    forall (jhigh: job) (jlow: job)
           (tskhigh: sporadic_task) (tsklow: sporadic_task)
           (sched: schedule) (t: time),
               (job_of jhigh tskhigh /\ job_of jlow tsklow /\ fp_higherprio order tskhigh tsklow)
               <-> hp jhigh jlow sched t.

