Require Import rt.util.all.
Require Import rt.model.task rt.model.job rt.model.arrival_sequence.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.

(* Definitions of FP, JLFP and JLDP priority relations. *)
Module Priority.

  Import SporadicTaskset ArrivalSequence.

  Section PriorityDefs.

    Section FP.

      (* Let Task denote any type of task. *)
      Variable Task: eqType.

      (* We define an FP policy as a relation between tasks. *)
      Definition FP_policy := rel Task.

    End FP.
    
    Section JLFP.

      (* Consider any job arrival sequence. *)
      Context {Job: eqType}.
      Variable arr_seq: arrival_sequence Job.
      
      (* We define a JLFP policy as a relation between jobs in the arrival sequence. *)
      Definition JLFP_policy := rel (JobIn arr_seq).

    End JLFP.

    Section JLDP.

      (* Consider any job arrival sequence. *)
      Context {Job: eqType}.
      Variable arr_seq: arrival_sequence Job.
      
      (* We define a JLDP policy as a time-dependent relation between jobs
         in the arrival sequence.
         Although this definition doesn't specify how the policy was constructed
         (e.g., whether it depends on the schedule, on job parameters, etc.), it is
         as general as possible. Knowing the priority of the jobs is sufficient
         to make scheduling decisions. *)
      Definition JLDP_policy := time -> rel (JobIn arr_seq).

    End JLDP.

  End PriorityDefs.

  (* Since FP policies are also JLFP and JLDP policies, we define
     next conversion functions to do the generalization. *)
  Section Generalization.

    (* Consider any arrival sequence of jobs spawned by tasks. *)
    Context {Task: eqType}.
    Context {Job: eqType}.
    Variable job_task: Job -> Task.
    Variable arr_seq: arrival_sequence Job.

    (* We show how to convert FP to JLFP,... *)
    Definition FP_to_JLFP (task_hp: FP_policy Task) : JLFP_policy arr_seq :=
      fun (jhigh jlow: JobIn arr_seq) =>
        task_hp (job_task jhigh) (job_task jlow).
    
    (* ...FP to JLDP, ... *)
    Definition FP_to_JLDP (task_hp: FP_policy Task) : JLDP_policy arr_seq :=
      fun (t: time) => FP_to_JLFP task_hp.

    (* ...and JLFP to JLDP. *)
    Definition JLFP_to_JLDP (job_hp: JLFP_policy arr_seq) : JLDP_policy arr_seq :=
      fun (t: time) => job_hp.
    
  End Generalization.

  (* Next we define properties of an FP policy. *)
  Section PropertiesFP.

    (* Assume that jobs are spawned by tasks. *)
    Context {Job: eqType}.
    Context {Task: eqType}.
    Variable job_task: Job -> Task.

    (* Consider any job arrival sequence... *)
    Variable arr_seq: arrival_sequence Job.

    (* ...and let task_priority be any FP policy. *)
    Variable task_priority: FP_policy Task.

    (* Now we define the properties. *)
    
    (* Whether the FP policy is reflexive. *)
    Definition FP_is_reflexive := reflexive task_priority.

    (* Whether the FP policy is irreflexive. *)
    Definition FP_is_irreflexive := irreflexive task_priority.

    (* Whether the FP policy is transitive. *)
    Definition FP_is_transitive := transitive task_priority.
    
    Section Antisymmetry.

      (* Consider any task set ts. *)
      Variable ts: seq Task.

      (* First we define whether task set ts is totally ordered with
         the priority. *)
      Definition FP_is_total_over_task_set :=
        total_over_list task_priority ts. 
      
      (* Then we define whether an FP policy is antisymmetric over task set ts, i.e.,
         whether the task set has unique priorities. *)
      Definition FP_is_antisymmetric_over_task_set :=
        antisymmetric_over_list task_priority ts. 
                  
    End Antisymmetry.

  End PropertiesFP. 
    
  (* Next, we define properties of a JLFP policy. *)
  Section PropertiesJLFP.

    (* Consider any JLFP policy. *)
    Context {Job: eqType}.
    Context {arr_seq: arrival_sequence Job}.
    Variable job_priority: JLFP_policy arr_seq.

    (* Now we define the properties. *)
    
    (* Whether the JLFP policy is reflexive. *)
    Definition JLFP_is_reflexive := reflexive job_priority.

    (* Whether the JLFP policy is irreflexive. *)
    Definition JLFP_is_irreflexive := irreflexive job_priority.

    (* Whether the JLFP policy is transitive. *)
    Definition JLFP_is_transitive := transitive job_priority.

    (* Whether the JLFP policy is total. *)
    Definition JLFP_is_total := total job_priority.

  End PropertiesJLFP.

  (* Next, we define properties of a JLDP policy. *)
  Section PropertiesJLDP.

    (* Consider any JLDP policy. *)
    Context {Job: eqType}.
    Context {arr_seq: arrival_sequence Job}.
    Variable job_priority: JLDP_policy arr_seq.

    (* Now we define the properties. *)
    
    (* Whether the JLDP policy is reflexive. *)
    Definition JLDP_is_reflexive :=
      forall t, reflexive (job_priority t).

    (* Whether the JLDP policy is irreflexive. *)
    Definition JLDP_is_irreflexive :=
      forall t, irreflexive (job_priority t).

    (* Whether the JLDP policy is transitive. *)
    Definition JLDP_is_transitive :=
      forall t, transitive (job_priority t).

    (* Whether the JLDP policy is total. *)
    Definition JLDP_is_total :=
      forall t, total (job_priority t).

  End PropertiesJLDP.

  (* Next we define some known FP policies. *)
  Section KnownFPPolicies.

    Context {Job: eqType}.
    Context {Task: eqType}.
    Variable task_period: Task -> time.
    Variable task_deadline: Task -> time.
    Variable job_task: Job -> Task.
    
    (* Rate-monotonic orders tasks by smaller periods. *)
    Definition RM (tsk1 tsk2: Task) :=
      task_period tsk1 <= task_period tsk2.

    (* Deadline-monotonic orders tasks by smaller relative deadlines. *)
    Definition DM (tsk1 tsk2: Task) :=
      task_deadline tsk1 <= task_deadline tsk2.

    Section Properties.

      Variable arr_seq: arrival_sequence Job.

      (* RM is reflexive. *)
      Lemma RM_is_reflexive : FP_is_reflexive RM.
      Proof.
        unfold FP_is_reflexive, reflexive, RM.
        by intros tsk; apply leqnn.
      Qed.

      (* RM is transitive. *)
      Lemma RM_is_transitive : FP_is_transitive RM.
      Proof.
        unfold FP_is_transitive, transitive, RM.
        by intros y x z; apply leq_trans.
      Qed.

      (* DM is reflexive. *)
      Lemma DM_is_reflexive : FP_is_reflexive DM.
      Proof.
        unfold FP_is_reflexive, reflexive, DM.
        by intros tsk; apply leqnn.
      Qed.

      (* DM is transitive. *)
      Lemma DM_is_transitive : FP_is_transitive DM.
      Proof.
        unfold FP_is_transitive, transitive, DM.
        by intros y x z; apply leq_trans.
      Qed.

    End Properties.

  End KnownFPPolicies.

  (* In this section, we define known JLFP policies. *)
  Section KnownJLFPPolicies.

    Context {Job: eqType}.
    Context {arr_seq: arrival_sequence Job}.
    Variable job_deadline: Job -> time.

    (* Earliest deadline first (EDF) orders jobs by absolute deadlines. *)
    Definition EDF (j1 j2: JobIn arr_seq) :=
      job_arrival j1 + job_deadline j1 <= job_arrival j2 + job_deadline j2.

    Section Properties.
      
      (* EDF is reflexive. *)
      Lemma EDF_is_reflexive : JLFP_is_reflexive EDF.
      Proof.
        by intros j; apply leqnn.
      Qed.

      (* EDF is transitive. *)
      Lemma EDF_is_transitive : JLFP_is_transitive EDF.
      Proof.
        by intros y x z; apply leq_trans.
      Qed.

      (* EDF is total. *)
      Lemma EDF_is_total : JLFP_is_total EDF.
      Proof.
        unfold EDF; intros x y.
        by case (leqP (job_arrival x + job_deadline x)
                      (job_arrival y + job_deadline y));
          [by rewrite orTb | by move/ltnW => ->].
      Qed.

    End Properties.

  End KnownJLFPPolicies.

  (* In this section, we define the notion of a possible interfering task. *)
  Section PossibleInterferingTasks.

    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.
    Variable task_deadline: sporadic_task -> time.

    Section FP.

      (* Assume an FP policy. *)
      Variable higher_eq_priority: FP_policy sporadic_task.

      (* Let tsk be the task to be analyzed ... *)
      Variable tsk: sporadic_task.

      (* ...and let tsk_other be another task. *)
      Variable tsk_other: sporadic_task.

      (* Under FP scheduling with constrained deadlines, tsk_other can only interfere
         with tsk if it is a different task with higher priority. *)
      Definition higher_priority_task :=
        higher_eq_priority tsk_other tsk &&
        (tsk_other != tsk).

    End FP.

    Section JLFP.

      (* Let tsk be the task to be analyzed ... *)
      Variable tsk: sporadic_task.

      (* ...and let tsk_other be another task. *)
      Variable tsk_other: sporadic_task.

      (* Under JLFP/JLDP scheduling with constrained deadlines, tsk_other can only interfere
         with tsk if it is a different task. *)
      Definition different_task := tsk_other != tsk.

    End JLFP.
    
  End PossibleInterferingTasks.  

End Priority.