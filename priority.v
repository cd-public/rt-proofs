Require Import Relations Arith Vbase extralib ExtraRelations task job helper schedule.
Set Implicit Arguments.

Record higher_priority : Type :=
{
  hp_rel:> schedule -> time -> job -> job ->Prop;

  hp_properties:
    << hpIrr: forall sched t, irreflexive (hp_rel sched t) >> /\
    << hpAntisym: forall sched t, antisymmetric _ (hp_rel sched t) >> /\
    << hpTrans: forall sched t, transitive _ (hp_rel sched t) >>
}.

(* Rate-Monotonic and Deadline-Monotonic priority order *)
Definition RM (tsk1 tsk2: sporadic_task) := task_period tsk1 < task_period tsk2.
Definition DM (tsk1 tsk2: sporadic_task) := task_deadline tsk1 < task_deadline tsk2.

(* Template for comparing task priority (with tie-break rule) *)
Definition fp_higher_priority (fp_order: sporadic_task -> sporadic_task -> Prop) :=
  fun tsk1 tsk2 => fp_order tsk1 tsk2 \/ task_id tsk1 < task_id tsk2.

(* Whether job priority is fixed priority *)
Definition fixed_priority (hp: higher_priority) (task_hp: sporadic_task -> sporadic_task -> Prop) :=
  forall (jhigh: job) (jlow: job) (tsk_high tsk_low: sporadic_task)
         (sched: schedule) (t: time)
         (JOBjhigh: job_of jhigh = Some tsk_high)
         (JOBjlow: job_of jlow = Some tsk_low),
           task_hp tsk_high tsk_low <-> hp sched t jhigh jlow.

(* Job-level fixed priority *)
Definition job_level_fixed_priority (hp: higher_priority) :=
  forall sched j1 j2 t t' (HP: hp sched t j1 j2), hp sched t' j1 j2.

Definition EDF (j1 j2: job) := job_deadline j1 < job_deadline j2.

(* Whether a priority order is schedule-independent *)
Definition schedule_independent (hp: higher_priority) :=
  forall (sched1 sched2: schedule) (ARR: arrives_at sched1 = arrives_at sched2) j1 j2 t,
    hp sched1 t j1 j2 = hp sched2 t j1 j2.