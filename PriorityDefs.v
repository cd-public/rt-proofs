Require Import Vbase ExtraRelations TaskDefs JobDefs ScheduleDefs
               ssreflect ssrbool eqtype ssrnat seq.
Set Implicit Arguments.

Module Priority.

Import SporadicTaskJob Schedule.

(* We define a policy as a relation between two jobs:
   j1 < j2 iff j1 has higher priority than j2. *)
Definition jldp_policy := schedule -> time -> job -> job -> bool.
Definition fp_policy := sporadic_task -> sporadic_task -> bool.

(* Assume that jobs have a total order (say, jobs ids) to break ties. *)
Parameter break_ties: sporadic_task -> sporadic_task -> bool.
Hypothesis break_ties_strict_total :
  forall (tsk1 tsk2: sporadic_task), break_ties tsk1 tsk2 (+) break_ties tsk2 tsk1.

Definition valid_jldp_policy (hp: jldp_policy) :=
  << hpIrr: forall sched t, irreflexive (hp sched t) >> /\
  << hpAsym: forall sched t, asymmetric (hp sched t) >> /\
  << hpTrans: forall sched t, transitive (hp sched t) >> /\
  << hpTotalTS:
       forall (sched: schedule) t j1 j2 arr1 arr2
              (NEQ: j1 <> j2) (NEQtsk: job_task j1 <> job_task j2)
              (ARRj1: arrives_at sched j1 arr1) (ARRj2: arrives_at sched j2 arr2),
         hp sched t j1 j2 \/ hp sched t j2 j1 >>.

(* Observations/TODO *)
(* 1) A higher-priority order serves to compare jobs of different tasks, since
      jobs of the same task already have precedence. Making the relation non-strict
      and total would only complicate the specification (a lot of
      "if j1 and j2 are from the same task" when defining RM and EDF). *)

Definition valid_fp_policy (task_hp: fp_policy) :=
  << hpIrr: irreflexive task_hp >> /\
  << hpAntisym: asymmetric task_hp >> /\
  << hpTrans: transitive task_hp >> /\
  << hpTotal: forall tsk1 tsk2 (NEQ: tsk1 <> tsk2),
                task_hp tsk1 tsk2 \/ task_hp tsk2 tsk1 >>.


(* Rate-Monotonic and Deadline-Monotonic priority order *)
Definition RM (tsk1 tsk2: sporadic_task) :=
  << LT_PER: (task_period tsk1 < task_period tsk2) >> ||
    << TIE: ((task_period tsk1 == task_period tsk2) && break_ties tsk1 tsk2) >>.

Definition DM (tsk1 tsk2: sporadic_task) :=
  << LT_DL: (task_deadline tsk1 < task_deadline tsk2) >> ||
    << TIE: ((task_deadline tsk1 == task_deadline tsk2) && break_ties tsk1 tsk2) >>.

Lemma rm_is_valid : valid_fp_policy RM.
Proof.
Admitted.
(*  have TIE := break_ties_strict_total.
  unfold valid_fp_policy, irreflexive, asymmetric, transitive, RM;
  repeat (split; try red).
  {
    intro x; apply/orP; unfold not; intro BUG; des; first by rewrite ltnn in BUG.
    by move: BUG => /andP BUG; des; rewrite ltnn in BUG0.
  }
  {
    intros x y BUG; des.
      by apply ltn_trans with (m := task_period y) in BUG; [by rewrite ltnn in BUG | by ins]. 
      by move: BUG =>/andP BUG; des; move: BUG =>/eqP BUG; rewrite BUG ltnn in BUG0.
      by move: BUG0 =>/andP BUG0; des; move: BUG0 =>/eqP BUG0; rewrite BUG0 ltnn in BUG.
      by move: BUG BUG0 => /andP BUG /andP BUG0; des; apply ltn_trans with (m := task_id x) in BUG1;
        [by rewrite ltnn in BUG1 | by ins].
  }
  {
    intros y x z; move => /orP XY /orP YZ; apply/orP; des.
      by left; apply ltn_trans with (n := task_period y).
      by left; move: XY => /andP XY; des; move: XY => /eqP XY; rewrite -XY in YZ.
      by left; move: YZ => /andP YZ; des; move: YZ => /eqP YZ; rewrite YZ in XY.
      by right; move: XY YZ => /andP XY /andP YZ; des; apply/andP; split;
        [by move: XY => /eqP XY; rewrite XY | by apply ltn_trans with (n := task_id y)].
  }
  {
    intros tsk1 tsk2 NEQ; destruct (ltngtP (task_period tsk1) (task_period tsk2)).
      by left; apply/orP; left.
      by right; apply/orP; left.
      rewrite e eq_refl 2!andTb 2!orFb.
      destruct (ltngtP (task_id tsk1) (task_id tsk2)) as [LT12 | LT21 | EQ];
        [by left | by right | by apply same_id_same_task in EQ]. 
  }
Qed.*)

Lemma dm_is_valid : valid_fp_policy DM.
Proof.
Admitted.

(*unfold valid_fp_policy, irreflexive, asymmetric, transitive, DM, break_ties;
  repeat (split; try red).
  {
    intro x; apply/orP; unfold not; intro BUG; des; first by rewrite ltnn in BUG.
    by move: BUG => /andP BUG; des; rewrite ltnn in BUG0.
  }
  {
    intros x y BUG; des.
      by apply ltn_trans with (m := task_deadline y) in BUG; [by rewrite ltnn in BUG | by ins]. 
      by move: BUG =>/andP BUG; des; move: BUG =>/eqP BUG; rewrite BUG ltnn in BUG0.
      by move: BUG0 =>/andP BUG0; des; move: BUG0 =>/eqP BUG0; rewrite BUG0 ltnn in BUG.
      by move: BUG BUG0 => /andP BUG /andP BUG0; des; apply ltn_trans with (m := task_id x) in BUG1;
        [by rewrite ltnn in BUG1 | by ins].
  }
  {
    intros y x z; move => /orP XY /orP YZ; apply/orP; des.
      by left; apply ltn_trans with (n := task_deadline y).
      by left; move: XY => /andP XY; des; move: XY => /eqP XY; rewrite -XY in YZ.
      by left; move: YZ => /andP YZ; des; move: YZ => /eqP YZ; rewrite YZ in XY.
      by right; move: XY YZ => /andP XY /andP YZ; des; apply/andP; split;
        [by move: XY => /eqP XY; rewrite XY | by apply ltn_trans with (n := task_id y)].
  }
  {
    intros tsk1 tsk2 NEQ; destruct (ltngtP (task_deadline tsk1) (task_deadline tsk2)).
      by left; apply/orP; left.
      by right; apply/orP; left.
      rewrite e eq_refl 2!andTb 2!orFb.
      destruct (ltngtP (task_id tsk1) (task_id tsk2)) as [LT12 | LT21 | EQ];
        [by left | by right | by apply same_id_same_task in EQ]. 
  }
Qed.*)

(* Relate task priority with job priority *)
Definition convert_fp_jldp (task_hp: fp_policy) (hp: jldp_policy) :=
  forall sched t jhigh jlow,
    hp sched t jhigh jlow =
      (<< NEQtsk: (job_task jhigh) != (job_task jlow) >> &&
       << HPtsk: task_hp (job_task jhigh) (job_task jlow) >>).

Lemma valid_fp_is_valid_jldp :
  forall hp task_hp (FP: valid_fp_policy task_hp) (CONV: convert_fp_jldp task_hp hp),
    valid_jldp_policy hp.
Proof.
Admitted.
(*
  unfold valid_fp_policy, valid_jldp_policy, convert_fp_jldp, irreflexive,
  asymmetric, transitive, ts_arrival_sequence; repeat (split; try red).
    by ins; rewrite CONV eq_refl /=.
    by intros sched t x y; rewrite 2!CONV; ins; des; eauto.
    intros sched t y x z; rewrite 3!CONV. move => /andP XY /andP YZ; apply/andP; split; des.
      by apply/negP; move/eqP => EQ; rewrite -> EQ in *; eauto.
      by apply hpTrans with (y := job_task y).
    intros sched t j1 j2 arr1 arr2 NEQ NEQjob ARR1 ARR2; des.
    rewrite 2!CONV; destruct (hpTotal (job_task j1) (job_task j2) NEQjob) as [HP | HP];
    rewrite HP andbT; [left | right]; apply/eqP; [by ins | by red; ins; intuition].
Qed.*)

(* Job-level fixed priority *)
Definition jlfp_policy (hp: jldp_policy) :=
  forall sched j1 j2 t t' (HP: hp sched t j1 j2), hp sched t' j1 j2.

Definition EDF (sched: schedule) (t: time) (j1 j2: job) :=
  (<< LTdl: job_arrival j1 + job_deadline j1 < job_arrival j2 + job_deadline j2 >>) ||
     (<< TIE: (job_arrival j1 + job_deadline j1 == job_arrival j2 + job_deadline j2) &&
                           break_ties (job_task j1) (job_task j2) >>).

Lemma edf_jlfp : jlfp_policy EDF. 
Proof.
  by unfold jlfp_policy, EDF.
Qed.

Lemma fp_is_jlfp :
  forall hp task_hp (CONV: convert_fp_jldp task_hp hp), jlfp_policy hp.
Proof.
  unfold jlfp_policy, valid_fp_policy, convert_fp_jldp; ins; des.
  rewrite -> CONV in *; move: HP => /andP HP; des.
  by apply/andP; split.
Qed.

Lemma edf_valid_policy : valid_jldp_policy EDF.
Proof.
Admitted.
(*  unfold valid_jldp_policy, EDF, irreflexive, asymmetric, transitive, break_ties;
  repeat (split; try red).
  {
    ins; apply/orP; unfold not; intro BUG; des; [| move: BUG => /andP BUG; des];
      by rewrite -> ltnn in *.
  }
  {
    intros sched t x y DL; des.
      by apply ltn_trans with (m := job_arrival y + job_deadline y) in DL; [by rewrite ltnn in DL|].
      by move: DL =>/andP DL; des; move: DL =>/eqP DL; rewrite DL ltnn in DL0.
      by move: DL0 =>/andP DL0; des; move: DL0 =>/eqP DL0; rewrite DL0 ltnn in DL.
      by move: DL DL0 => /andP DL /andP DL0; des; apply ltn_trans with
                                                  (m := task_id (job_task x)) in DL1;
        [by rewrite ltnn in DL1 | by ins].
  }
  {
    intros sched t y x z; move => /orP XY /orP YZ; apply/orP; des.
      by left; apply ltn_trans with (n := job_arrival y + job_deadline y).
      by left; move: XY => /andP XY; des; move: XY => /eqP XY; rewrite -XY in YZ.
      by left; move: YZ => /andP YZ; des; move: YZ => /eqP YZ; rewrite YZ in XY.
      by right; move: XY YZ => /andP XY /andP YZ; des; apply/andP; split;
        [by move: XY => /eqP XY; rewrite XY | by apply ltn_trans with (n := task_id (job_task y))].
  }
  {
    intros sched t j1 j2 arr1 arr2 NEQ NEQtsk ARR1 ARR2.
    destruct (ltngtP (job_arrival j1 + job_deadline j1) (job_arrival j2 + job_deadline j2)).
      by left; apply/orP; left.
      by right; apply/orP; left.
      rewrite e eq_refl 2!andTb 2!orFb.
      by destruct (ltngtP (task_id (job_task j1)) (task_id (job_task j2))) as [LT12 | LT21 | EQ];
        [by left | by right | by apply same_id_same_task in EQ].     
  }
Qed.*)

(* Whether a priority order is schedule-independent *)
Definition schedule_independent (hp: jldp_policy) :=
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
  unfold schedule_independent, convert_fp_jldp, RM; repeat (split; try red); rewrite 2!CONV; ins.
Qed.

End Priority.