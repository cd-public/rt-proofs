Require Import Vbase ExtraRelations TaskDefs JobDefs ScheduleDefs (*TaskArrivalDefs*)
               ssreflect ssrbool eqtype ssrnat seq.
Set Implicit Arguments.

Module Priority.

  Import SporadicTask Schedule.

  Section PriorityDefs.

    Context {sporadic_task: eqType}.
    Context {Job: eqType}.
    Variable num_cpus: nat.
    Variable arr_seq: arrival_sequence Job.

    (* All the priority relations are non-strict, i.e., they specify that
       "job_high has higher priority than (or the same priority as) job_low".
       We define two relations: between jobs (JLDP) and between tasks (JLFP). *)

    (* JLDP policy is a generic relation between two jobs of an arrival sequence.
       To ensure they can be defined arbitrarily, jldp_policy is parameterized
       by schedule and time. *)
    Definition jldp_policy := time -> JobIn arr_seq -> JobIn arr_seq -> bool.

    (* FP policy is simply a relation between tasks.
       Because our model of processor platform is based on a generic JLDP policy,
       we generate a JLDP policy from an FP policy whenever required. *)
    Definition fp_policy := sporadic_task -> sporadic_task -> bool.

    Section ValidJLFPPolicy.

      Variable is_higher_priority: jldp_policy.

      (* A policy is reflexive, since a job has the same priority as itself. *)
      Definition jlfp_is_reflexive :=
        forall t, reflexive (is_higher_priority t).

      (* A policy is transitive. *)
      Definition jlfp_is_transitive :=
        forall t, transitive (is_higher_priority t).
      
      (* A policy is total, since it must know the priority of any two jobs at any time. *)
      Definition jlfp_is_total :=
        forall (sched: schedule num_cpus arr_seq)
               (j1 j2: JobIn arr_seq) t,
          is_higher_priority sched t j1 j2 \/ is_higher_priority sched t j2 j1.

      (* A JLDP policy is valid iff it satisfies the three properties.
         Note that, for generality, we don't enforce antisymmetry and allow multiple
         jobs with same priority. *)
      Definition valid_jldp_policy :=
        jlfp_is_reflexive /\ jlfp_is_transitive /\ jlfp_is_total.

    End ValidJLFPPolicy.

    Section ValidFPPolicy.

      Variable is_higher_priority: fp_policy.

      Definition fp_is_reflexive := reflexive is_higher_priority.

      Definition fp_is_transitive := transitive is_higher_priority.
      
      Definition fp_is_total :=
        forall tsk1 tsk2,
          is_higher_priority tsk1 tsk2 \/ is_higher_priority tsk2 tsk1.

      (* We enforce the same restrictions for FP policy: reflexive, transitive, total. *)
      Definition valid_fp_policy :=
        fp_is_reflexive /\ fp_is_transitive /\ fp_is_total.

    End ValidFPPolicy.

  End PriorityDefs.
  
  Section RateDeadlineMonotonic.

    (* Rate-Monotonic and Deadline-Monotonic priority order *)
    Definition RM (tsk1 tsk2: sporadic_task) := task_period tsk1 <= task_period tsk2.

    Definition DM (tsk1 tsk2: sporadic_task) := task_deadline tsk1 <= task_deadline tsk2.

    Lemma rm_is_valid : valid_fp_policy RM.
    Proof.
      unfold valid_fp_policy, fp_is_reflexive, fp_is_transitive, RM;
        repeat (split; try red); first by ins.
      by intros x y z XY YZ; apply leq_trans with (n := task_period x).
      by intros tsk1 tsk2; destruct (leqP (task_period tsk1) (task_period tsk2));
        [by left | by right; apply ltnW].
    Qed.

    Lemma dm_is_valid : valid_fp_policy DM.
    Proof.
      unfold valid_fp_policy, fp_is_reflexive, fp_is_transitive, DM;
      repeat (split; try red); first by ins.
        by intros x y z; apply leq_trans.
        by intros tsk1 tsk2; destruct (leqP (task_deadline tsk1) (task_deadline tsk2));
          [by left | by right; apply ltnW].
    Qed.

  End RateDeadlineMonotonic.

  Section GeneralizeFP.

    Context {Job: eqType}.
    Variable job_task: Job -> sporadic_task.
    Variable arr_seq: arrival_sequence Job.
    Variable num_cpus: nat.
    
    Definition fp_to_jldp (task_hp: fp_policy) : jldp_policy num_cpus arr_seq :=
      fun (sched: schedule num_cpus arr_seq) (t: time) (jhigh jlow: JobIn arr_seq) =>
        task_hp (job_task jhigh) (job_task jlow).

    Lemma valid_fp_is_valid_jldp :
      forall task_hp (FP: valid_fp_policy task_hp),
        valid_jldp_policy (fp_to_jldp task_hp).
    Proof.
      unfold fp_to_jldp, valid_fp_policy, valid_jldp_policy,
             fp_is_reflexive, fp_is_transitive, fp_is_total,
             jlfp_is_reflexive, jlfp_is_transitive, jlfp_is_total, reflexive, transitive.
      ins; destruct FP as [REFL [TRANS TOTAL]]; repeat (split; try red); des; last by ins.
        by ins; rewrite REFL.
        by intros sched t y x z; apply TRANS.
    Qed.

  End GeneralizeFP.

  Section JLFPDefs.

    Context {Job: eqType}.
    Context {num_cpus: nat}.
    Context {arr_seq: arrival_sequence Job}.

    Variable is_higher_priority: jldp_policy num_cpus arr_seq.

    (* JLFP policy is a JLDP policy where the priorities do not vary with time. *)
    Definition is_jlfp_policy (is_higher_priority: jldp_policy num_cpus arr_seq) :=
      forall sched j1 j2 t t',
        is_higher_priority sched t j1 j2 -> is_higher_priority sched t' j1 j2.

    (* Lemma: every FP policy is a JLFP policy. *)
    Variable job_task: Job -> sporadic_task.
    Lemma fp_is_jlfp :
      forall fp_higher_priority,
        is_jlfp_policy (fp_to_jldp job_task fp_higher_priority).
    Proof.
      by unfold is_jlfp_policy, valid_fp_policy.
    Qed.

  End JLFPDefs.

  Section EDFDefs.

    Context {Job: eqType}.
    Context {num_cpus: nat}.
    Context {arr_seq: arrival_sequence Job}.
    Variable job_deadline: Job -> nat.
      
    Definition EDF (sched: schedule num_cpus arr_seq) (t: time) (j1 j2: JobIn arr_seq) :=
      job_arrival j1 + job_deadline j1 <= job_arrival j2 + job_deadline j2.

    (* Lemma: EDF is a JLFP policy. *)
    Lemma edf_jlfp : is_jlfp_policy EDF. 
    Proof.
      by unfold is_jlfp_policy, EDF.
    Qed.

    Lemma edf_valid_policy : valid_jldp_policy EDF.
    Proof.
      unfold valid_jldp_policy, EDF, jlfp_is_reflexive, jlfp_is_transitive, reflexive, transitive.
      repeat (split; try red).
        by ins; apply leqnn.
        by intros sched t y x z; apply leq_trans.
        by intros sched j1 j2 t;
          destruct (leqP (job_arrival j1 + job_deadline j1) (job_arrival j2 + job_deadline j2));
            [by left | by right; apply ltnW].
    Qed.

  End EDFDefs.

  Section ScheduleIndependent.

    Context {Job: eqType}.
    Context {num_cpus: nat}.
    Context {arr_seq: arrival_sequence Job}.
    
    (* Whether a priority order is schedule-independent *)
    Definition schedule_independent (hp: jldp_policy num_cpus arr_seq) :=
      forall (sched1 sched2: schedule num_cpus arr_seq),
        hp sched1 = hp sched2.

    Variable job_deadline: Job -> nat.
    Lemma edf_schedule_independent : schedule_independent (EDF job_deadline).
    Proof.
      by unfold schedule_independent, EDF; ins.
    Qed.
      
    Variable job_task: Job -> sporadic_task.
    Lemma fp_schedule_independent :
      forall task_hp,
        schedule_independent (fp_to_jldp job_task task_hp).
    Proof. 
      by unfold schedule_independent, fp_to_jldp.
    Qed.
      
  End ScheduleIndependent.

End Priority.


(*Section BasicDefinitions.

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

End BasicDefinitions.*)


  