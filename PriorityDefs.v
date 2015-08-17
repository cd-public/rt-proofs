Require Import Vbase ExtraRelations TaskDefs JobDefs ScheduleDefs TaskArrivalDefs
               ssreflect ssrbool eqtype ssrnat seq.
Set Implicit Arguments.

Module Priority.

Import SporadicTaskJob Schedule.

(* We define a policy as a relation between two jobs:
   j1 <= j2 iff j1 has higher priority than (or equal to) j2. *)
Definition jldp_policy := schedule -> time -> job -> job -> bool.
Definition fp_policy := sporadic_task -> sporadic_task -> bool.

Definition valid_jldp_policy (hp: jldp_policy) :=
  << hpIrr: forall sched t, reflexive (hp sched t) >> /\
  << hpTrans: forall sched t, transitive (hp sched t) >> /\
  << hpTotalTS: forall (sched: schedule) t
                       j1 arr1 (ARRj1: arrives_at sched j1 arr1)
                       j2 arr2 (ARRj2: arrives_at sched j2 arr2),
                  hp sched t j1 j2 \/ hp sched t j2 j1 >>.

Definition valid_fp_policy (task_hp: fp_policy) :=
  << hpIrr: reflexive task_hp >> /\
  << hpTrans: transitive task_hp >> /\
  << hpTotal: forall tsk1 tsk2, task_hp tsk1 tsk2 \/ task_hp tsk2 tsk1 >>.

(* Rate-Monotonic and Deadline-Monotonic priority order *)
Definition RM (tsk1 tsk2: sporadic_task) := task_period tsk1 <= task_period tsk2.

Definition DM (tsk1 tsk2: sporadic_task) := task_deadline tsk1 <= task_deadline tsk2.

Lemma rm_is_valid : valid_fp_policy RM.
Proof.
  unfold valid_fp_policy, reflexive, antisymmetric, transitive, RM;
  repeat (split; try red); first by ins.
    by intros x y z XY YZ; apply leq_trans with (n := task_period x).
    by intros tsk1 tsk2; destruct (leqP (task_period tsk1) (task_period tsk2));
      [by left | by right; apply ltnW].
Qed.

Lemma dm_is_valid : valid_fp_policy DM.
Proof.
  unfold valid_fp_policy, reflexive, antisymmetric, transitive, DM;
  repeat (split; try red); first by ins.
    by intros x y z; apply leq_trans.
    by intros tsk1 tsk2; destruct (leqP (task_deadline tsk1) (task_deadline tsk2));
      [by left | by right; apply ltnW].
Qed.

Definition fp_to_jldp (task_hp: fp_policy) :=
  fun (sched: schedule) (t: time) jhigh jlow =>
    task_hp (job_task jhigh) (job_task jlow).

Lemma valid_fp_is_valid_jldp :
  forall task_hp (FP: valid_fp_policy task_hp), valid_jldp_policy (fp_to_jldp task_hp).
Proof.
  unfold fp_to_jldp, valid_fp_policy, valid_jldp_policy, reflexive, transitive;
  repeat (split; try red); des; first by ins.
    by intros sched t y x z; apply hpTrans with (y := (job_task y)).
    by ins; apply hpTotal.
Qed.

Definition jlfp_policy (hp: jldp_policy) :=
  forall sched j1 j2 t t' (HP: hp sched t j1 j2), hp sched t' j1 j2.

Definition EDF (sched: schedule) (t: time) (j1 j2: job) :=
  job_arrival j1 + job_deadline j1 <= job_arrival j2 + job_deadline j2.

Lemma edf_jlfp : jlfp_policy EDF. 
Proof.
  by unfold jlfp_policy, EDF.
Qed.

Lemma fp_is_jlfp :
  forall task_hp, jlfp_policy (fp_to_jldp task_hp).
Proof.
  by unfold jlfp_policy, valid_fp_policy.
Qed.

Lemma edf_valid_policy : valid_jldp_policy EDF.
Proof.
  unfold valid_jldp_policy, EDF, reflexive, transitive;
  repeat (split; try red); first by ins.
    by intros sched t y x z; apply leq_trans.
    by intros sched t j1 arr1 ARR1 j2 arr2 ARR2;
       destruct (leqP (job_arrival j1 + job_deadline j1) (job_arrival j2 + job_deadline j2));
       [by left | by right; apply ltnW].
Qed.

(* Whether a priority order is schedule-independent *)
Definition schedule_independent (hp: jldp_policy) :=
  forall (sched1 sched2: schedule)
         (ARR: arr_seq_of sched1 = arr_seq_of sched2),
    hp sched1 = hp sched2.

Lemma edf_schedule_independent : schedule_independent EDF.
Proof.
  by unfold schedule_independent, EDF; ins.
Qed.

Lemma fp_schedule_independent :
  forall task_hp, schedule_independent (fp_to_jldp task_hp).
Proof.
  by unfold schedule_independent, fp_to_jldp.
Qed.

Section BasicDefinitions.

Variable higher_eq_priority: jldp_policy.
Variable sched: schedule.
Variable t: time.

Definition num_pending_jobs :=
  count (fun j => pending sched j t) (all_arrivals sched t).

Definition num_scheduled_jobs :=
  count (fun j => scheduled sched j t) (all_arrivals sched t).

(* Whether a job jhigh can preempt jlow at time t *)
Definition interferes_with (jlow jhigh: job) :=
  scheduled sched jhigh t &&
  higher_eq_priority sched t jhigh jlow &&
  (jhigh != jlow).

Definition num_interfering_jobs (jlow: job) :=
  count (interferes_with jlow) (all_arrivals sched t).

End BasicDefinitions.

End Priority.