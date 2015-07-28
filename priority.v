Require Import List Relations Classical Arith Vbase extralib ExtraRelations task job task_arrival helper schedule.
Set Implicit Arguments.

(* Task ids are assumed to uniquely identify a task. Necessary to break ties in priority. *)
Hypothesis same_id_same_task : forall tsk1 tsk2 (EQid: task_id tsk1 = task_id tsk2), tsk1 = tsk2. 
Definition break_ties (tsk1 tsk2: sporadic_task) := task_id tsk1 < task_id tsk2.

Definition task_hp_relation := sporadic_task -> sporadic_task -> Prop.
Definition job_hp_relation := job -> job -> Prop.
Definition sched_job_hp_relation := schedule -> time -> job_hp_relation.

Definition valid_jldp_policy (hp_rel: sched_job_hp_relation) :=
  << hpIrr: forall sched t, irreflexive (hp_rel sched t) >> /\
  << hpAsym: forall sched t, asymmetric (hp_rel sched t) >> /\
  << hpTrans: forall sched t, transitive _ (hp_rel sched t) >> /\
  << hpTotalTS:
       forall (sched: schedule) t j1 j2 arr1 arr2
              (NEQ: j1 <> j2) (NEQtsk: job_task j1 <> job_task j2)
              (ARRj1: arrives_at sched j1 arr1)
              (ARRj2: arrives_at sched j2 arr2),
         hp_rel sched t j1 j2 \/ hp_rel sched t j2 j1 >>.

(* Observations/TODO *)
(* 1) A higher-priority order serves to compare jobs of different tasks, since
      jobs of the same task already have precedence. Making the relation non-strict
      and total would only complicate the specification (a lot of
      "if j1 and j2 are from the same task" when defining RM and EDF). *)

Definition valid_fp_policy (task_hp_rel: task_hp_relation) :=
  << hpIrr: irreflexive task_hp_rel >> /\
  << hpAntisym: asymmetric task_hp_rel >> /\
  << hpTrans: transitive _ task_hp_rel >> /\
  << hpTotal: forall tsk1 tsk2 (NEQ: tsk1 <> tsk2), task_hp_rel tsk1 tsk2 \/ task_hp_rel tsk2 tsk1 >>.

(* Rate-Monotonic and Deadline-Monotonic priority order *)
Definition RM (tsk1 tsk2: sporadic_task) :=
  << LTper: task_period tsk1 < task_period tsk2 >> \/
  << TIE: (task_period tsk1 = task_period tsk2 /\ break_ties tsk1 tsk2) >>.

Definition DM (tsk1 tsk2: sporadic_task) :=
  << LTper: task_deadline tsk1 < task_deadline tsk2 >> \/
  << TIE: (task_deadline tsk1 = task_deadline tsk2 /\ break_ties tsk1 tsk2) >>.

Lemma rm_is_valid : valid_fp_policy RM.
Proof.
  unfold valid_fp_policy, irreflexive, asymmetric, transitive, RM, break_ties;
  repeat (split; try red); ins; try by (des; intuition).
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

Lemma dm_is_valid : valid_fp_policy DM.
Proof.
  unfold valid_fp_policy, irreflexive, asymmetric, transitive, DM, break_ties;
  repeat (split; try red); ins; try by (des; intuition).
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
Definition convert_fp_jldp (task_hp: task_hp_relation) (hp: sched_job_hp_relation) :=
  forall sched t jhigh jlow,
    hp sched t jhigh jlow <->
      (<< NEQtsk: (job_task jhigh) <> (job_task jlow) >> /\
       << HPtsk: task_hp (job_task jhigh) (job_task jlow) >>).

Lemma valid_fp_is_valid_jldp :
  forall (*ts sched*) hp task_hp
         (*(ARRts: ts_arrival_sequence ts sched) (* All jobs come from taskset *)*)
         (FP: valid_fp_policy task_hp)
         (CONV: convert_fp_jldp task_hp hp), valid_jldp_policy hp.
Proof.
  unfold valid_fp_policy, valid_jldp_policy, convert_fp_jldp, irreflexive,
  asymmetric, transitive, ts_arrival_sequence; repeat (split; try red); ins; des;
  rewrite CONV in *; try rewrite CONV in *; des; repeat (split; try red); eauto.
  by unfold not; intro EQ; rewrite EQ in *; eauto.
  {
    specialize (hpTotal (job_task j1) (job_task j2) NEQtsk).
    des; [left|right]; split; eauto.
  }
Qed.

(* Job-level fixed priority *)
Definition jlfp_policy (hp: sched_job_hp_relation) :=
  forall sched j1 j2 t t' (HP: hp sched t j1 j2), hp sched t' j1 j2.

Definition EDF (sched: schedule) (t: time) (j1 j2: job) :=
  exists r1 r2, << ARR1: arrives_at sched j1 r1 >> /\
                << ARR2: arrives_at sched j2 r2 >> /\
                (<< LTper: r1 + job_deadline j1 < r2 + job_deadline j2 >> \/
                 <<  TIE: (r1 + job_deadline j1 = r2 + job_deadline j2 /\
                           break_ties (job_task j1) (job_task j2)) >>).

Lemma edf_jlfp : jlfp_policy EDF. 
Proof.
  by unfold jlfp_policy, EDF.
Qed.

Lemma fp_is_jlfp :
  forall hp task_hp (CONV: convert_fp_jldp task_hp hp), jlfp_policy hp.
Proof.
  unfold jlfp_policy, valid_fp_policy, convert_fp_jldp; ins; des.
  rewrite CONV in *; eauto.
Qed.

Lemma edf_valid_policy : valid_jldp_policy EDF.
Proof.
  unfold valid_jldp_policy, EDF, irreflexive, asymmetric, transitive, break_ties;
  repeat (split; try red); ins;
  have arrProp := arr_properties (arr_list sched).
    by des; [assert (r1 = r2) by eauto using NOMULT; subst|]; intuition.
    by des; assert (r0 = r2); assert (r1 = r3); eauto using NOMULT; by intuition.
    des; assert (r1 = r3); eauto using NOMULT; subst; exists r0,r2; repeat split; eauto.
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

Lemma fp_schedule_independent :
  forall hp tsk_hp (CONV: convert_fp_jldp tsk_hp hp), schedule_independent hp.
Proof.
  unfold schedule_independent, convert_fp_jldp, RM; repeat (split; try red);
  ins; des; rewrite CONV in *; eauto.
Qed.