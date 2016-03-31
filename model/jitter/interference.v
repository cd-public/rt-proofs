Add LoadPath "../../" as rt.

Require Import rt.util.all.
Require Import rt.model.jitter.task rt.model.jitter.job rt.model.jitter.schedule
               rt.model.jitter.priority rt.model.jitter.workload.
Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Module Interference.

  Import ScheduleWithJitter ScheduleOfSporadicTask Priority Workload.

  (* We import some of the basic definitions, but we need to re-define almost everything
     since the definition of backlogged (and thus the definition of interference)
     changes with jitter. *)
  Require Import rt.model.basic.interference.
  Export Interference.
  
  Section InterferenceDefs.

    Context {sporadic_task: eqType}.
    Context {Job: eqType}.
    Variable job_cost: Job -> time.
    Variable job_task: Job -> sporadic_task.
    Variable job_jitter: Job -> time.

    (* Assume any job arrival sequence...*)
    Context {arr_seq: arrival_sequence Job}.

    (* ... and any schedule. *)
    Context {num_cpus: nat}.
    Variable sched: schedule num_cpus arr_seq.

    (* Consider any job j that incurs interference. *)
    Variable j: JobIn arr_seq.

    (* Recall the definition of backlogged (pending and not scheduled). *)
    Let job_is_backlogged (t: time) :=
      backlogged job_cost job_jitter sched j t.

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
         (job_is_backlogged t && scheduled sched job_other t).

    End JobInterference.
    
    Section TaskInterference.

      (* In order to define task interference, consider any interfering task tsk_other. *)
      Variable tsk_other: sporadic_task.
    
      Definition schedules_job_of_tsk (cpu: processor num_cpus) (t: time) :=
        match (sched cpu t) with
          | Some j' => job_task j' == tsk_other
          | None => false
        end.

      (* We know that tsk is scheduled at time t if there exists a processor
         scheduling a job of tsk. *)
      Definition task_is_scheduled (t: time) :=
        [exists cpu in processor num_cpus, schedules_job_of_tsk cpu t].

      (* We define the total interference caused by tsk during [t1, t2) as
         the cumulative time in which j is backlogged while tsk is scheduled. *)
      Definition task_interference (t1 t2: time) :=
        \sum_(t1 <= t < t2)
          (job_is_backlogged t && task_is_scheduled t).

    End TaskInterference.

    Section TaskInterferenceJobList.

      Variable tsk_other: sporadic_task.

      Definition task_interference_joblist (t1 t2: time) :=
        \sum_(j <- jobs_scheduled_between sched t1 t2 | job_task j == tsk_other)
         job_interference j t1 t2.

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

      Lemma job_interference_le_delta :
        forall j_other t1 delta,
          job_interference j_other t1 (t1 + delta) <= delta.
      Proof.
        unfold job_interference; intros j_other t1 delta.
        apply leq_trans with (n := \sum_(t1 <= t < t1 + delta) 1);
          first by apply leq_sum; ins; apply leq_b1.
        by rewrite big_const_nat iter_addn mul1n addn0 addKn leqnn.
      Qed.

      Lemma job_interference_le_service :
        forall j_other t1 t2,
          job_interference j_other t1 t2 <= service_during sched j_other t1 t2.
      Proof.
        intros j_other t1 t2; unfold job_interference, service_during.
        apply leq_trans with (n := \sum_(t1 <= t < t2) scheduled sched j_other t);
          first by apply leq_sum; ins; destruct (job_is_backlogged i); rewrite ?andTb ?andFb.
        apply leq_sum; intros t _.
        destruct (scheduled sched j_other t) eqn:SCHED; last by done.
        move: SCHED => /existsP EX; destruct EX as [cpu]; move: H => /andP [IN SCHED].
        unfold service_at; rewrite (bigD1 cpu); last by done.
        by apply leq_trans with (n := 1).
      Qed.
      
      Lemma task_interference_le_workload :
        forall tsk t1 t2,
          task_interference tsk t1 t2 <= workload job_task sched tsk t1 t2.
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
        apply ltn_addr; unfold service_of_task, schedules_job_of_tsk in *.
        by destruct (sched cpu t); [rewrite HAScpu | by done].
      Qed.

    End BasicLemmas.

    (* If we assume no intra-task parallelism, the two definitions
       of interference are the same. *)
    Section EquivalenceWithPerJobInterference.

      Hypothesis H_no_intratask_parallelism:
        jobs_of_same_task_dont_execute_in_parallel job_task sched.
      
      Lemma interference_eq_interference_joblist :
        forall tsk t1 t2,
          task_interference tsk t1 t2 = task_interference_joblist tsk t1 t2.
      Proof.
        intros tsk t1 t2; unfold task_interference, task_interference_joblist, job_interference.
        rewrite [\sum_(j <- jobs_scheduled_between _ _ _ | _) _]exchange_big /=.
        apply eq_big_nat; unfold service_at; intros t LEt.
        destruct (job_is_backlogged t && task_is_scheduled tsk t) eqn:BACK.
        {
          move: BACK => /andP [BACK SCHED]; symmetry.
          move: SCHED => /existsP SCHED; destruct SCHED as [x IN]; move: IN => /andP [IN SCHED].
          unfold schedules_job_of_tsk in SCHED; desf.
          rename SCHED into EQtsk0, Heq into SCHED; move: EQtsk0 => /eqP EQtsk0.
          assert (SCHEDULED: scheduled sched j0 t).
          {
            unfold scheduled, scheduled_on.
            apply/existsP; exists x; apply/andP; split; [by done | by rewrite SCHED eq_refl].
          }
          rewrite big_mkcond (bigD1_seq j0) /=; last by rewrite undup_uniq.
          {
            rewrite EQtsk0 BACK SCHEDULED andbT big_mkcond.
            rewrite (eq_bigr (fun x => 0));
              first by rewrite big_const_seq iter_addn mul0n addn0 addn0.
            intros j1 _; desf; try by done.
            apply/eqP; rewrite eqb0; apply/negP; unfold not; intro SCHEDULED'.
            exploit (H_no_intratask_parallelism j0 j1 t); try by eauto.
          }
          {
            rewrite mem_undup.
            apply mem_bigcat_nat with (j := t); first by auto.
            apply mem_bigcat_ord with (j := x); first by apply ltn_ord.
            by rewrite SCHED mem_seq1.
          }
        }
        {
          rewrite big_mkcond (eq_bigr (fun x => 0));
            first by rewrite big_const_seq iter_addn mul0n addn0.
          intros i _; desf; rewrite // ?BACK ?andFb //.
          unfold task_is_scheduled in BACK.
          apply negbT in BACK; rewrite negb_exists in BACK.
          move: BACK => /forallP BACK.
          assert (NOTSCHED: scheduled sched i t = false).
          {
            apply negbTE; rewrite negb_exists; apply/forallP.
            intros x; rewrite negb_and.
            specialize (BACK x); rewrite negb_and in BACK; ins.
            unfold schedules_job_of_tsk in BACK; unfold scheduled_on.
            destruct (sched x t) eqn:SCHED; last by ins.
            apply/negP; unfold not; move => /eqP BUG; inversion BUG; subst.
            by move: BACK => /negP BACK; apply BACK.
          }
          by rewrite NOTSCHED andbF.
        }
      Qed.

    End EquivalenceWithPerJobInterference.

    (* If we don't assume intra-task parallelism, the per-job interference
       bounds the actual interference. *)
    Section BoundUsingPerJobInterference.

      Lemma interference_le_interference_joblist :
        forall tsk t1 t2,
          task_interference tsk t1 t2 <= task_interference_joblist tsk t1 t2.
      Proof.
        intros tsk t1 t2; unfold task_interference, task_interference_joblist, job_interference.
        rewrite [\sum_(j <- jobs_scheduled_between _ _ _ | _) _]exchange_big /=.
        rewrite big_nat_cond [\sum_(_ <= _ < _ | true)_]big_nat_cond.
        apply leq_sum; intro t; rewrite andbT; intro LT.
        destruct (job_is_backlogged t && task_is_scheduled tsk t) eqn:BACK;
          last by done.
        move: BACK => /andP [BACK SCHED].
        move: SCHED => /existsP SCHED; destruct SCHED as [x IN]; move: IN => /andP [IN SCHED].
        unfold schedules_job_of_tsk in SCHED; desf.
        rename SCHED into EQtsk0, Heq into SCHED; move: EQtsk0 => /eqP EQtsk0.
        rewrite big_mkcond (bigD1_seq j0) /=; last by rewrite undup_uniq.
        {
          rewrite -addn1 addnC; apply leq_add; last by done.
          rewrite EQtsk0 BACK andTb.
          apply eq_leq; symmetry; apply/eqP; rewrite eqb1.
          unfold scheduled, scheduled_on.
          by apply/exists_inP; exists x; [by done | by rewrite SCHED].
        }
        {
          unfold jobs_scheduled_between.
          rewrite mem_undup.
          apply mem_bigcat_nat with (j := t); first by auto.
          unfold jobs_scheduled_at.
          apply mem_bigcat_ord with (j := x); first by apply ltn_ord.
          by unfold make_sequence; rewrite SCHED mem_seq1.
        }
      Qed.
        
    End BoundUsingPerJobInterference.

    Section CorrespondenceWithService.

      Variable t1 t2: time.
      
      (* Assume that jobs do not execute in parallel, ...*)
      Hypothesis no_parallelism:
        jobs_dont_execute_in_parallel sched.

      (* ..., and that jobs only execute after the jitter
         and no longer than their execution costs. *)
      Hypothesis jobs_execute_after_jitter:
        jobs_execute_after_jitter job_jitter sched.
      Hypothesis completed_jobs_dont_execute:
        completed_jobs_dont_execute job_cost sched.

      Let j_has_actually_arrived_by := has_actually_arrived_by job_jitter j.
      
      (* If job j had actually by time t1 and did not yet
         complete by time t2, ...*)
      Hypothesis job_has_actually_arrived : j_has_actually_arrived_by t1.
      Hypothesis job_is_not_complete : ~~ completed job_cost sched j t2.

      (* then the service received by j during [t1, t2) equals
         the cumulative time in which it did not incur interference. *)
      Lemma complement_of_interf_equals_service :
        \sum_(t1 <= t < t2) service_at sched j t =
          t2 - t1 - total_interference t1 t2.
      Proof.
        unfold completed, total_interference, job_is_backlogged,
               backlogged, service_during, pending.
        rename no_parallelism into NOPAR,
               jobs_execute_after_jitter into JITTER,
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