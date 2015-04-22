Add LoadPath "/home/felipec/dev/coq/rt-scheduling-spec".
Require Import Coq.Arith.Lt.
Require Import job.
Require Import helper.
Require Import schedule.

(* Generic priority order for jobs in a schedule at some time t *)
Definition higher_priority := job -> job -> schedule -> time -> Prop.

(* Job priority must be a partial order: irreflexive, antisymetric, transitive. *)
Record valid_priority (hp: higher_priority) : Prop :=
  { hp_irreflexive: forall (j: job) (sched: schedule) (t: time), ~ hp j j sched t;
    hp_antisymmetric: forall (j1 j2: job) (sched: schedule) (t: time),
                         hp j1 j2 sched t /\ hp j2 j1 sched t -> j1 = j2;
    hp_transitive: forall (j1 j2 j3: job) (sched: schedule) (t: time),
                       hp j1 j2 sched t /\ hp j2 j3 sched t -> hp j1 j3 sched t 
  }.

(* Generic fixed priority order for two tasks *)
Definition fp_order := sporadic_task -> sporadic_task -> Prop.

(* Rate-Monotonic and Deadline-Monotonic priority order *)
Definition RM (tsk1 tsk2: sporadic_task) : Prop :=
    task_period tsk1 < task_period tsk2.
Definition DM (tsk1 tsk2: sporadic_task) : Prop :=
    task_deadline tsk1 < task_deadline tsk2.

(* Template for comparing task priority (with tie-break rule) *)
Definition fp_higherprio (order: fp_order) (tsk1 tsk2: sporadic_task) : Prop :=
    order tsk1 tsk2 \/ task_id tsk1 < task_id tsk2.

(* Whether job priority is fixed priority *)
Definition fixed_priority (hp: higher_priority) (order: fp_order) : Prop :=
    forall (jhigh: job) (jlow: job)
           (tskhigh tsklow: sporadic_task)
           (sched: schedule) (t: time),
               (job_of jhigh tskhigh /\ job_of jlow tsklow /\ fp_higherprio order tskhigh tsklow)
               <-> hp jhigh jlow sched t.

(* Proof that RM policy is a partial order for jobs *)
Lemma RM_priority_valid :
    forall (hp: higher_priority), fixed_priority hp RM -> valid_priority hp.
Proof.
    intros.
    unfold fixed_priority in H.
    split. intros.
    specialize (H j j).
    assert (H0 := excluded_middle (exists tsk, job_of j tsk)).
    inversion H0. inversion H1 as [tsk].
    specialize H with tsk tsk sched t.
    inversion H.
    assert (H5 := excluded_middle (hp j j sched t)).
    inversion H5. apply H4 in H6. inversion H6 as [_ [_ H7]].
    unfold fp_higherprio in H7.
    inversion H7. unfold RM in H8.
    assert (H9 := lt_irrefl (task_period tsk)). eauto.
    assert (H9 := lt_irrefl (task_id tsk)). eauto.
    apply H6.
    Admitted. (*TODO finish this proof*)

(* Job-level fixed priority *)
Definition job_level_fixed_priority (hp: higher_priority) :=
    forall (sched: schedule) (j1: job) (j2: job) (t: time) (t': time),
        hp j1 j2 sched t -> hp j1 j2 sched t'.

Definition EDF (j1 j2: job) : Prop := job_deadline j1 < job_deadline j2.