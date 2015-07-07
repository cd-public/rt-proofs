Require Import List Relations Classical Arith Vbase extralib ExtraRelations task job task_arrival helper schedule.
Set Implicit Arguments.

Hypothesis same_id_same_task : (* Necessary to break the ties in priority *)
  forall tsk1 tsk2, task_id tsk1 = task_id tsk2 -> tsk1 = tsk2.

Definition task_hp_relation := sporadic_task -> sporadic_task -> Prop.
Definition job_hp_relation := job -> job -> Prop.
Definition sched_job_hp_relation := schedule -> time -> job -> job -> Prop.

Definition higher_priority (sched: schedule) (t: time) (hp_rel: job_hp_relation) :=
  << hpIrr: irreflexive hp_rel >> /\
  << hpAsym: asymmetric hp_rel >> /\
  << hpTrans: transitive _ hp_rel >> /\
  << hpTotalTS:
       forall j1 j2 arr1 arr2 (NEQ: j1 <> j2) (NEQtsk: job_task j1 <> job_task j2)
              (ARRj1: arrives_at sched j1 arr1) (ARRj2: arrives_at sched j2 arr2),
                hp_rel j1 j2 \/ hp_rel j2 j1 >>. (* Should work for JLDP *)

(* Observations/TODO *)
(* 1) A higher-priority order serves to compare jobs of different tasks, since
      jobs of the same task already have precedence. Making the relation total
      over any job would only complicate the specification (a lot of
      "if j1 and j2 come from the same task" everywhere). *)

Definition task_higher_priority (ts: taskset) (task_hp_rel: task_hp_relation) :=
  << hpIrr: irreflexive task_hp_rel >> /\
  << hpAntisym: asymmetric task_hp_rel >> /\
  << hpTrans: transitive _ task_hp_rel >> /\
  << hpTotal:
       forall ts tsk1 tsk2 (IN1: In tsk1 ts) (IN2: In tsk2 ts) (NEQ: tsk1 <> tsk2), 
         task_hp_rel tsk1 tsk2 \/ task_hp_rel tsk2 tsk1 >>.

(*Definition task_precedence (sched: schedule) (j1 j2: job) :=
  forall t1 t2, job_task j1 = job_task j2 /\ t1 < t2 /\ 
                arrives_at sched j1 t1 /\ arrives_at sched j2 t2.*)

(* Rate-Monotonic and Deadline-Monotonic priority order *)
Definition RM (tsk1 tsk2: sporadic_task) :=
  << LTper: task_period tsk1 < task_period tsk2 >> \/
  << TIE: (task_period tsk1 = task_period tsk2 /\ task_id tsk1 < task_id tsk2) >>.

Definition DM (tsk1 tsk2: sporadic_task) :=
  << LTper: task_deadline tsk1 < task_deadline tsk2 >> \/
  << TIE: (task_deadline tsk1 = task_deadline tsk2 /\ task_id tsk1 < task_id tsk2) >>.

Lemma rm_valid : forall ts, task_higher_priority ts RM.
Proof.
  unfold task_higher_priority, irreflexive, asymmetric, transitive, RM;
    repeat (split; try red); ins.
  by des; intuition.
  by des; intuition.
  by des; try rewrite TIE in *; eauto using lt_trans, eq_trans.
  destruct (lt_eq_lt_dec (task_period tsk1) (task_period tsk2)) as [DEC2 | LTper];
  [destruct DEC2 as [LTper| EQper] |].
    by left; left.
    destruct (lt_eq_lt_dec (task_id tsk1) (task_id tsk2)) as [DEC3 | LTid];
    [destruct DEC3 as [LTid| EQid]|].
      by left; right.
      by apply same_id_same_task in EQid; eauto; intuition.
      by right; right.      
    by right; left.
Qed.

Lemma dm_valid : forall ts, task_higher_priority ts DM.
Proof.
  unfold task_higher_priority, irreflexive, asymmetric, transitive, DM;
    repeat (split; try red); ins.
  by des; intuition.
  by des; intuition.
  by des; try rewrite TIE in *; eauto using lt_trans, eq_trans.
  destruct (lt_eq_lt_dec (task_deadline tsk1) (task_deadline tsk2)) as [DEC2 | LTdl];
  [destruct DEC2 as [LTdl| EQper] |].
    by left; left.
    destruct (lt_eq_lt_dec (task_id tsk1) (task_id tsk2)) as [DEC3 | LTid];
    [destruct DEC3 as [LTid| EQid]|].
      by left; right.
      by apply same_id_same_task in EQid; eauto; intuition.
      by right; right.      
    by right; left.
Qed.

(* Relate task priority with job priority *)
Definition fixed_priority (ts: taskset) (hp: job_hp_relation) (task_hp: task_hp_relation) :=
  forall jhigh jlow tsk_high tsk_low,
    hp jhigh jlow <->
    (<< NEQtsk: tsk_high <> tsk_low >> /\
     << JOBjhigh: job_task jhigh = tsk_high>> /\
     << JOBjlow: job_task jlow = tsk_low >> /\
     << HPtsk: task_hp tsk_high tsk_low >>).

(* Job-level fixed priority *)
Definition job_level_fixed_priority (hp: sched_job_hp_relation) :=
  forall sched j1 j2 t t' (HP: hp sched t j1 j2), hp sched t' j1 j2.

Definition EDF (sched: schedule) (t: time) (j1 j2: job) :=
  exists r1 r2, << ARR1: arrives_at sched j1 r1 >> /\
                << ARR2: arrives_at sched j2 r2 >> /\
                (<< LTper: r1 + job_deadline j1 < r2 + job_deadline j2 >> \/
                 <<  TIE: (r1 + job_deadline j1 = r2 + job_deadline j2 /\
                           task_id (job_task j1) < task_id (job_task j2)) >>).

Lemma edf_jlfp : job_level_fixed_priority EDF. 
Proof.
  by unfold job_level_fixed_priority, EDF.
Qed.

Lemma fp_implies_jlfp :
  forall ts sched t hp task_hp
         (ARRts: ts_arrival_sequence ts sched) (* All jobs come from taskset *)
         (VALIDthp: task_higher_priority ts task_hp)
         (FP: fixed_priority ts hp task_hp), higher_priority sched t hp.
Proof.
  unfold task_higher_priority, fixed_priority, higher_priority, irreflexive,
  asymmetric, transitive, ts_arrival_sequence; ins; repeat (split; try red); ins; des.

  by rewrite FP with (tsk_high := job_task x) (tsk_low := job_task x) in *; des; eauto.
  by rewrite FP with (tsk_high := job_task x) (tsk_low := job_task y) in H;
     rewrite FP with (tsk_high := job_task y) (tsk_low := job_task x) in H0; des; eauto.
  by rewrite FP with (tsk_high := job_task x) (tsk_low := job_task z);
     rewrite FP with (tsk_high := job_task x) (tsk_low := job_task y) in H;
     rewrite FP with (tsk_high := job_task y) (tsk_low := job_task z) in H0;
     repeat (split; try red); des; [unfold not; intro EQ; rewrite EQ in *|]; eauto.
  { apply ARRts in ARRj1; apply ARRts in ARRj2.
    destruct (hpTotal ts (job_task j1) (job_task j2) ARRj1 ARRj2 NEQtsk).
      by left; rewrite FP with (tsk_high := job_task j1) (tsk_low := job_task j2); split; eauto.
      by right; rewrite FP with (tsk_high := job_task j2) (tsk_low := job_task j1); split; eauto.
  }
Qed.

Lemma edf_valid : forall sched t, higher_priority sched t (EDF sched t).
Proof.
  unfold higher_priority, EDF, irreflexive, asymmetric, transitive;
  repeat (split; try red); ins.
    by des; [assert (r1 = r2) by eauto using no_multiple_arrivals; subst|]; intuition.
    by des; assert (r0 = r2); assert (r1 = r3); eauto using no_multiple_arrivals; by intuition.
    des; assert (r1 = r3); eauto using no_multiple_arrivals; subst; exists r0,r2; repeat split; eauto.
      by left; eauto using lt_trans.
      by left; rewrite TIE.
      by left; rewrite <- TIE.
      by right; split; [omega | eauto using lt_trans].
  destruct (lt_eq_lt_dec (arr1 + job_deadline j1) (arr2 + job_deadline j2)) as [xxx | LTdl];
  [destruct xxx as [LTdl| EQdl] |].
    by left; exists arr1, arr2; repeat split; eauto.
    destruct (lt_eq_lt_dec (task_id (job_task j1)) (task_id (job_task j2))) as [DEC3 | LTid];
    [destruct DEC3 as [LTid| EQid]|].
      by left; exists arr1, arr2; repeat split; eauto.
      by apply same_id_same_task in EQid; intuition.
      by right; exists arr2, arr1; repeat split; eauto.
    by right; exists arr2, arr1; repeat split; eauto.
Qed.

(* Whether a priority order is schedule-independent *)
Definition schedule_independent (hp: sched_job_hp_relation) :=
  forall (sched1 sched2: schedule) (ARR: arrives_at sched1 = arrives_at sched2) j1 j2 t,
    hp sched1 t j1 j2 <-> hp sched2 t j1 j2.

Lemma edf_schedule_independent : schedule_independent EDF.
Proof.
  unfold schedule_independent, EDF; repeat (split; try red); ins; des; rewrite ARR in *;
  exists r1, r2; repeat split; eauto.
Qed.