Add LoadPath "../../" as rt.
Require Import rt.util.Vbase rt.util.lemmas rt.util.divround.
Require Import rt.model.basic.task rt.model.basic.job rt.model.basic.schedule
               rt.model.basic.priority rt.model.basic.workload.
Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Module Interference.

  Import Schedule ScheduleOfSporadicTask Priority Workload.

  Section PossibleInterferingTasks.

    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.
    Variable task_deadline: sporadic_task -> time.

    Section FP.

      (* Assume an FP policy. *)
      Variable higher_eq_priority: FP_policy sporadic_task.

      (* Under constrained deadlines, tsk_other can only interfere with tsk
         if it's a different task with higher or equal priority. *)
      Definition fp_can_interfere_with (tsk tsk_other: sporadic_task) :=
        higher_eq_priority tsk_other tsk && (tsk_other != tsk).

    End FP.

    Section JLFP.

      (* Under JLFP/JLDP policies, any two different tasks can interfere with
         each other. *)
      Definition jldp_can_interfere_with (tsk tsk_other: sporadic_task) :=
        tsk_other != tsk.

    End JLFP.
    
  End PossibleInterferingTasks.
  
  Section InterferenceDefs.

    Context {sporadic_task: eqType}.
    Context {Job: eqType}.
    Variable job_cost: Job -> time.
    Variable job_task: Job -> sporadic_task.

    (* Assume any job arrival sequence...*)
    Context {arr_seq: arrival_sequence Job}.

    (* ... and any schedule. *)
    Context {num_cpus: nat}.
    Variable sched: schedule num_cpus arr_seq.

    (* Consider any job j that incurs interference. *)
    Variable j: JobIn arr_seq.

    (* Recall the definition of backlogged (pending and not scheduled). *)
    Let job_is_backlogged (t: time) :=
      backlogged job_cost sched j t.

    Section TotalInterference.
      
      (* First, we define the total interference incurred by job j during [t1, t2)
         as the cumulative time in which j is backlogged in this interval. *)
      Definition total_interference (t1 t2: time) :=
        \sum_(t1 <= t < t2) job_is_backlogged t.

    End TotalInterference.
    
    Section JobInterference.

      (* Let job_other be a job that interferes with j. *)
      Variable job_other: JobIn arr_seq.

      (* The interference caused by job_other is defined as follows. *)
      Definition job_interference (t1 t2: time) :=
        \sum_(t1 <= t < t2)
          \sum_(cpu < num_cpus)
            (job_is_backlogged t && scheduled_on sched job_other cpu t).

    End JobInterference.

    Section JobInterferenceSequential.

      (* Let job_other be a job that interferes with j. *)
      Variable job_other: JobIn arr_seq.

      (* If jobs are sequential, the interference caused by job_other
         is defined as follows. *)
      Definition job_interference_sequential (t1 t2: time) :=
        \sum_(t1 <= t < t2)
         (job_is_backlogged t && scheduled sched job_other t).

    End JobInterferenceSequential.

    Section TaskInterference.

      (* In order to define task interference, consider any interfering task tsk_other. *)
      Variable tsk_other: sporadic_task.
      
      Definition schedules_job_of_task (cpu: processor num_cpus) (t: time) :=
        match (sched cpu t) with
          | Some j' => job_task j' == tsk_other
          | None => false
        end.

      (* We know that tsk is scheduled at time t if there exists a processor
         scheduling a job of tsk. *)
      Definition task_is_scheduled (t: time) :=
        [exists cpu in processor num_cpus, schedules_job_of_task cpu t].

      (* We define the total interference caused by tsk during [t1, t2) as the
         cumulative time in which j is backlogged while tsk is scheduled. *)
      Definition task_interference (t1 t2: time) :=
        \sum_(t1 <= t < t2)
          \sum_(cpu < num_cpus)
            (job_is_backlogged t && schedules_job_of_task cpu t).

    End TaskInterference.

    Section TaskInterferenceSequential.

      (* In order to define task interference, consider any interfering task tsk_other. *)
      Variable tsk_other: sporadic_task.
    
      (* If jobs are sequential, we define the total interference caused by
         tsk during [t1, t2) as the cumulative time in which j is backlogged
         while tsk is scheduled. *)
      Definition task_interference_sequential (t1 t2: time) :=
        \sum_(t1 <= t < t2)
          (job_is_backlogged t && task_is_scheduled tsk_other t).

    End TaskInterferenceSequential.

    Section TaskInterferenceJobList.

      Variable tsk_other: sporadic_task.

      Definition task_interference_sequential_joblist (t1 t2: time) :=
        \sum_(j <- jobs_scheduled_between sched t1 t2 | job_task j == tsk_other)
         job_interference_sequential j t1 t2.

    End TaskInterferenceJobList.

    Section BasicLemmas.

      (* Interference cannot be larger than the considered time window. *)
      Lemma total_interference_le_delta :
        forall t1 t2,
          total_interference t1 t2 <= t2 - t1.
      Proof.
        unfold total_interference; intros t1 t2.
        apply leq_trans with (n := \sum_(t1 <= t < t2) 1);
          first by apply leq_sum; ins; apply leq_b1.
        by rewrite big_const_nat iter_addn mul1n addn0 leqnn.
      Qed.

      Lemma job_interference_seq_le_delta :
        forall j_other t1 delta,
          job_interference_sequential j_other t1 (t1 + delta) <= delta.
      Proof.
        unfold job_interference; intros j_other t1 delta.
        apply leq_trans with (n := \sum_(t1 <= t < t1 + delta) 1);
          first by apply leq_sum; ins; apply leq_b1.
        by rewrite big_const_nat iter_addn mul1n addn0 addKn leqnn.
      Qed.

      Lemma job_interference_seq_le_service :
        forall j_other t1 t2,
          job_interference_sequential j_other t1 t2 <= service_during sched j_other t1 t2.
      Proof.
        intros j_other t1 t2; unfold job_interference_sequential, service_during.
        apply leq_trans with (n := \sum_(t1 <= t < t2) scheduled sched j_other t);
          first by apply leq_sum; ins; destruct (job_is_backlogged i); rewrite ?andTb ?andFb.
        apply leq_sum; intros t _.
        destruct (scheduled sched j_other t) eqn:SCHED; last by done.
        move: SCHED => /existsP EX; destruct EX as [cpu]; move: H => /andP [IN SCHED].
        unfold service_at; rewrite (bigD1 cpu); last by done.
        by apply leq_trans with (n := 1).
      Qed.

      Lemma job_interference_le_service :
        forall j_other t1 t2,
          job_interference j_other t1 t2 <= service_during sched j_other t1 t2.
      Proof.
        intros j_other t1 t2; unfold job_interference, service_during.
        apply leq_sum; intros t _.
        unfold service_at; rewrite [\sum_(_ < _ | scheduled_on _ _ _  _)_]big_mkcond.
        apply leq_sum; intros cpu _.
        destruct (job_is_backlogged t); [rewrite andTb | by rewrite andFb].
        by destruct (scheduled_on sched j_other cpu t).
      Qed.
      
      Lemma task_interference_seq_le_workload :
        forall tsk t1 t2,
          task_interference_sequential tsk t1 t2 <= workload job_task sched tsk t1 t2.
      Proof.
        unfold task_interference, workload; intros tsk t1 t2.
        apply leq_sum; intros t _.
        rewrite -mulnb -[\sum_(_ < _) _]mul1n.
        apply leq_mul; first by apply leq_b1.
        destruct (task_is_scheduled tsk t) eqn:SCHED; last by ins.
        unfold task_is_scheduled in SCHED.
        move: SCHED =>/exists_inP SCHED.
        destruct SCHED as [cpu _ HAScpu].
        rewrite -> bigD1 with (j := cpu); simpl; last by ins.
        apply ltn_addr; unfold service_of_task, schedules_job_of_task in *.
        by destruct (sched cpu t); [rewrite HAScpu | by done].
      Qed.

      Lemma task_interference_le_workload :
        forall tsk t1 t2,
          task_interference tsk t1 t2 <= workload job_task sched tsk t1 t2.
      Proof.
        unfold task_interference, workload; intros tsk t1 t2.
        apply leq_sum; intros t _.
        apply leq_sum; intros cpu _.
        destruct (job_is_backlogged t); [rewrite andTb | by rewrite andFb].
        unfold schedules_job_of_task, service_of_task.
        by destruct (sched cpu t).
      Qed.

    End BasicLemmas.

    (* The sequential per-job interference bounds the actual interference. *)
    Section BoundUsingPerJobInterference.

      Lemma interference_le_interference_joblist :
        forall tsk t1 t2,
          task_interference_sequential tsk t1 t2 <=
          task_interference_sequential_joblist tsk t1 t2.
      Proof.
        intros tsk t1 t2; unfold task_interference_sequential, task_interference_sequential_joblist, job_interference.
        rewrite [\sum_(j <- jobs_scheduled_between _ _ _ | _) _]exchange_big /=.
        rewrite big_nat_cond [\sum_(_ <= _ < _ | true)_]big_nat_cond.
        apply leq_sum; intro t; rewrite andbT; intro LT.
        destruct (job_is_backlogged t && task_is_scheduled tsk t) eqn:BACK;
          last by done.
        move: BACK => /andP [BACK SCHED].
        move: SCHED => /existsP SCHED; destruct SCHED as [x IN]; move: IN => /andP [IN SCHED].
        unfold schedules_job_of_task in SCHED; desf.
        rename SCHED into EQtsk0, Heq into SCHED; move: EQtsk0 => /eqP EQtsk0.
        rewrite big_mkcond (bigD1_seq j0) /=; last by rewrite undup_uniq.
        {
          rewrite -addn1 addnC; apply leq_add; last by done.
          rewrite EQtsk0 eq_refl BACK andTb.
          apply eq_leq; symmetry; apply/eqP; rewrite eqb1.
          unfold scheduled, scheduled_on.
          by apply/exists_inP; exists x; [by done | by rewrite SCHED].
        }
        {
          unfold jobs_scheduled_between.
          rewrite mem_undup.
          apply mem_bigcat_nat with (j := t); first by done.
          unfold jobs_scheduled_at.
          apply mem_bigcat_ord with (j := x); first by apply ltn_ord.
          by unfold make_sequence; rewrite SCHED mem_seq1 eq_refl.
        }
      Qed.
        
    End BoundUsingPerJobInterference.

    Section CorrespondenceWithService.

      Variable t1 t2: time.
      
      (* Assume that jobs do not execute in parallel, ...*)
      Hypothesis no_parallelism:
        jobs_dont_execute_in_parallel sched.

      (* ..., and that jobs only execute after they arrived
         and no longer than their execution costs. *)
      Hypothesis jobs_must_arrive_to_execute:
        jobs_must_arrive_to_execute sched.
      Hypothesis completed_jobs_dont_execute:
        completed_jobs_dont_execute job_cost sched.

      (* If job j had already arrived at time t1 and did not yet
         complete by time t2, ...*)
      Hypothesis job_has_arrived :
        has_arrived j t1.
      Hypothesis job_is_not_complete :
        ~~ completed job_cost sched j t2.

      (* ... then the service received by j during [t1, t2) equals
         the cumulative time in which it did not incur interference. *)
      Lemma complement_of_interf_equals_service :
        \sum_(t1 <= t < t2) service_at sched j t =
          t2 - t1 - total_interference t1 t2.
      Proof.
        unfold completed, total_interference, job_is_backlogged,
               backlogged, service_during, pending.
        rename no_parallelism into NOPAR,
               jobs_must_arrive_to_execute into MUSTARRIVE,
               completed_jobs_dont_execute into COMP,
               job_is_not_complete into NOTCOMP.

        (* Reorder terms... *)
        apply/eqP; rewrite subh4; first last.
        {
          rewrite -[t2 - t1]mul1n -[1*_]addn0 -iter_addn -big_const_nat.
          by apply leq_sum; ins; apply leq_b1.
        }
        {
          rewrite -[t2 - t1]mul1n -[1*_]addn0 -iter_addn -big_const_nat.
          by apply leq_sum; ins; apply service_at_most_one. 
        }
        apply/eqP.
        
        apply eq_trans with (y := \sum_(t1 <= t < t2)
                                    (1 - service_at sched j t));
          last first.
        {
          apply/eqP; rewrite <- eqn_add2r with (p := \sum_(t1 <= t < t2)
                                               service_at sched j t).
          rewrite subh1; last first.
            rewrite -[t2 - t1]mul1n -[1*_]addn0 -iter_addn -big_const_nat.
            by apply leq_sum; ins; apply service_at_most_one.
          rewrite -addnBA // subnn addn0 -big_split /=.
          rewrite -[t2 - t1]mul1n -[1*_]addn0 -iter_addn -big_const_nat.
          apply/eqP; apply eq_bigr; ins; rewrite subh1;
            [by rewrite -addnBA // subnn addn0 | by apply service_at_most_one].
        }
        rewrite big_nat_cond [\sum_(_ <= _ < _ | true)_]big_nat_cond.
        apply eq_bigr; intro t; rewrite andbT; move => /andP [GEt1 LTt2].
        destruct (~~ scheduled sched j t) eqn:SCHED; last first.
        {
          apply negbFE in SCHED; unfold scheduled in *.
          move: SCHED => /exists_inP SCHED; destruct SCHED as [cpu INcpu SCHEDcpu].
          rewrite andbF; apply/eqP.
          rewrite -(eqn_add2r (service_at sched j t)) add0n.
          rewrite subh1; last by apply service_at_most_one.
          rewrite -addnBA // subnn addn0.
          rewrite eqn_leq; apply/andP; split; first by apply service_at_most_one.
          unfold service_at; rewrite (bigD1 cpu) /=; last by apply SCHEDcpu.
          by apply leq_trans with (n := 1).
        }
        rewrite not_scheduled_no_service in SCHED.
        move: SCHED => /eqP SCHED.
        rewrite SCHED subn0 andbT; apply/eqP; rewrite eqb1.
        apply/andP; split; first by apply leq_trans with (n := t1).
        apply/negP; unfold not; intro BUG.
        apply completion_monotonic with (t' := t2) in BUG; [ | by ins | by apply ltnW].
        by rewrite BUG in NOTCOMP.
      Qed.
      
    End CorrespondenceWithService.

  End InterferenceDefs.

End Interference.