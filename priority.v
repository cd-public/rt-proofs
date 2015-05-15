Require Import Coq.Arith.Lt.
Require Import task.
Require Import job.
Require Import helper.
Require Import schedule.
Require Import Coq.Classes.RelationClasses.

Record higher_priority : Type :=
  {
    _hp:> schedule -> time -> job -> job ->Prop;

    hp_irreflexive: forall (j: job) (sched: schedule) (t: time), ~ _hp sched t j j;
    hp_antisymmetric: forall (j1 j2: job) (sched: schedule) (t: time),
                         _hp sched t j1 j2 /\ _hp sched t j2 j1 -> j1 = j2;
    hp_transitive: forall (j1 j2 j3: job) (sched: schedule) (t: time),
                       _hp sched t j1 j2 /\ _hp sched t j2 j3 -> _hp sched t j1 j3
  }.

(* Rate-Monotonic and Deadline-Monotonic priority order *)
Definition RM (tsk1 tsk2: sporadic_task) : Prop :=
    task_period tsk1 < task_period tsk2.
Definition DM (tsk1 tsk2: sporadic_task) : Prop :=
    task_deadline tsk1 < task_deadline tsk2.

(* Template for comparing task priority (with tie-break rule) *)
Definition fp_higher_priority (fp_order: sporadic_task -> sporadic_task -> Prop)
                                : sporadic_task -> sporadic_task -> Prop :=
     fun (tsk1 tsk2: sporadic_task) =>
     fp_order tsk1 tsk2 \/ task_id tsk1 < task_id tsk2.

(* Whether job priority is fixed priority *)
Definition fixed_priority (hp: higher_priority)
                          (task_hp: sporadic_task -> sporadic_task -> Prop) : Prop :=
    forall (jhigh: job) (jlow: job)
           (tsk_high tsk_low: sporadic_task)
           (sched: schedule) (t: time),
               (job_of jhigh = Some tsk_high
               /\ job_of jlow = Some tsk_low
               /\ task_hp tsk_high tsk_low)
                   <-> hp sched t jhigh jlow.

(* Proof that RM policy is a partial order for jobs *)
(*Lemma RM_priority_valid :
    forall (hp: higher_priority), fixed_priority hp RM -> valid_priority hp.
Proof.
    intros.
    unfold fixed_priority in H.
    split. intros.
    specialize (H j j).
    assert (H0 := excluded_middle (exists tsk, job_of j = Some tsk)).
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
    Admitted. (*TODO finish this proof*)*)

(* Job-level fixed priority *)
Definition job_level_fixed_priority (hp: higher_priority) :=
    forall (sched: schedule) (j1: job) (j2: job) (t: time) (t': time),
        hp sched t j1 j2 -> hp sched t' j1 j2.

Definition EDF (j1 j2: job) : Prop := job_deadline j1 < job_deadline j2.

(* Whether a priority order is schedule-independent *)
Definition schedule_independent (hp: higher_priority) : Prop :=
    forall (sched1 sched2: schedule),
        arrives_at sched1 = arrives_at sched2 ->
            forall (j1 j2: job) (t: time), hp sched1 t j1 j2 = hp sched2 t j1 j2.
