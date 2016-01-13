Require Import Vbase task schedule job priority interference util_lemmas
               ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.

Module Platform.

  Import ScheduleOfSporadicTask SporadicTaskset Interference Priority.

  Section SchedulingInvariants.
    
    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> nat.
    Variable task_period: sporadic_task -> nat.
    Variable task_deadline: sporadic_task -> nat.
    
    Context {Job: eqType}.
    Variable job_cost: Job -> nat.
    Variable job_deadline: Job -> nat.
    Variable job_task: Job -> sporadic_task.
    
    (* Assume any job arrival sequence... *)
    Context {arr_seq: arrival_sequence Job}.

    (* Consider any schedule such that...*)
    Variable num_cpus: nat.
    Variable rate: Job -> processor num_cpus -> nat.
    Variable sched: schedule num_cpus arr_seq.

    (* Assume that we have a task set where all tasks have valid
       parameters and restricted deadlines. *)
    Variable ts: taskset_of sporadic_task.

    Section FP.

      (* Given an FP policy, ...*)
      Variable higher_eq_priority: fp_policy sporadic_task.
 
      (* the global scheduling invariant states that if a job is
         backlogged, then all the processors are busy with jobs
         of higher-priority tasks. *)
      Definition FP_scheduling_invariant_holds :=
        forall (tsk: sporadic_task) (j: JobIn arr_seq) (t: time),
          tsk \in ts ->
          job_task j = tsk ->
          backlogged job_cost rate sched j t ->
          count
            (fun tsk_other : sporadic_task =>
               is_interfering_task_fp higher_eq_priority tsk tsk_other &&
                 task_is_scheduled job_task sched tsk_other t) ts = num_cpus.

    End FP.

    Section JLDP.

      (* Given a JLFP/JLDP policy, ...*)
      Variable higher_eq_priority: jldp_policy arr_seq.

      (* ... the global scheduling invariant states that at any time t,
         if a job J is backlogged, then all processors are busy with
         jobs of higher-priority. *)
      Definition JLFP_JLDP_scheduling_invariant_holds :=
        forall (j: JobIn arr_seq) (t: time),
          backlogged job_cost rate sched j t ->
          count
              (fun j_other => higher_eq_priority t j_other j)
              (jobs_scheduled_at sched t)
            = num_cpus.

      Section BasicLemmas.

        Hypothesis H_invariant_holds :
          JLFP_JLDP_scheduling_invariant_holds.

        (* The job which is interfering has higher or equal priority to the interfered one. *)
        Lemma interfering_job_has_higher_eq_prio :
          forall j j_other t,
            backlogged job_cost rate sched j t ->
            scheduled sched j_other t ->
            higher_eq_priority t j_other j.
        Proof.
          intros j j_other t BACK SCHED.
          exploit H_invariant_holds; [by apply BACK | intro COUNT].
          destruct (higher_eq_priority t j_other j) eqn:LOW; first by done.
          apply negbT in LOW.
          generalize SCHED; unfold scheduled in SCHED; intro SCHED'.
          move: SCHED => /existsP EX; destruct EX as [cpu H].
          move: H => /andP [_ /eqP SCHED].
          assert (ATMOST: size (jobs_scheduled_at sched t) <= num_cpus).
          {
            apply size_bigcat_ord; [by apply cpu|].
            by ins; unfold make_sequence; destruct (sched x t).
          }
          rewrite -(count_predC (fun j_other => higher_eq_priority t j_other j)) COUNT in ATMOST.
          assert (BUG: num_cpus < num_cpus).
          {
            apply leq_trans with (n := num_cpus + count (predC (fun j_other => higher_eq_priority t j_other j)) (jobs_scheduled_at sched t));
              last by done.
            rewrite -{1}[num_cpus]addn0 ltn_add2l -has_count.
            apply/hasP; exists j_other; last by done.
            unfold jobs_scheduled_at.
            apply mem_bigcat_ord with (j := cpu);
              first by apply ltn_ord.
            by unfold make_sequence; rewrite SCHED mem_seq1 eq_refl.
          }
          by rewrite ltnn in BUG.
        Qed.

        (* Assume the task set has no duplicates. *)
        Hypothesis H_ts_is_a_set: uniq ts.
        
        (* Assume all jobs are from the taskset, ... *)
        Hypothesis H_all_jobs_from_taskset:
          forall (j: JobIn arr_seq), job_task j \in ts.
        (* ..., a single job does not execute in parallel, ...*)
        Hypothesis H_no_parallelism:
          jobs_dont_execute_in_parallel sched.
        (* ... and jobs from the same task do not execute in parallel. *)
        Hypothesis H_no_intra_task_parallelism:
          jobs_of_same_task_dont_execute_in_parallel job_task sched.

        Lemma scheduled_jobs_unique :
          jobs_dont_execute_in_parallel sched ->
          forall t,
            uniq (jobs_scheduled_at sched t).
        Proof.
          intros _ t; rename H_no_parallelism into SEQUENTIAL.
          unfold jobs_dont_execute_in_parallel in SEQUENTIAL.
          clear -SEQUENTIAL.
          unfold jobs_scheduled_at.
          induction num_cpus; first by rewrite big_ord0.
          {
            
            rewrite big_ord_recr cat_uniq; apply/andP; split.
            {
              apply bigcat_ord_uniq;
                first by intro i; unfold make_sequence; desf.
              intros x i1 i2 IN1 IN2; unfold make_sequence in *.
              desf; move: Heq0 Heq => SOME1 SOME2.
              rewrite mem_seq1 in IN1; rewrite mem_seq1 in IN2.
              move: IN1 IN2 => /eqP IN1 /eqP IN2; subst x j0.
              specialize (SEQUENTIAL j t (widen_ord (leqnSn n) i1)
                             (widen_ord (leqnSn n) i2) SOME1 SOME2).
              by inversion SEQUENTIAL; apply ord_inj.
            }
            apply/andP; split; last by unfold make_sequence; destruct (sched ord_max).
            {
              rewrite -all_predC; apply/allP; unfold predC; simpl.
              intros x INx.
              unfold make_sequence in INx.
              destruct (sched ord_max t) eqn:SCHED;
                last by rewrite in_nil in INx.
              apply/negP; unfold not; intro IN'.
              have EX := mem_bigcat_ord_exists _ x n.
              apply EX in IN'; des; clear EX.
              unfold make_sequence in IN'.
              desf; rename Heq into SCHEDi.
              rewrite mem_seq1 in INx; rewrite mem_seq1 in IN'.
              move: INx IN' => /eqP INx /eqP IN'; subst x j0.
              specialize (SEQUENTIAL j t ord_max (widen_ord (leqnSn n) i) SCHED SCHEDi).
              inversion SEQUENTIAL; destruct i as [i EQ]; simpl in *.
              clear SEQUENTIAL SCHEDi.
              by rewrite H0 ltnn in EQ.
            }
          }
        Qed.

        (* If a job isn't scheduled, the processor are busy with interfering tasks. *)
        Lemma cpus_busy_with_interfering_tasks :
          forall (j: JobIn arr_seq) tsk t,
            job_task j = tsk ->
            backlogged job_cost rate sched j t ->
            count
              (fun j : sporadic_task =>
                 is_interfering_task_jlfp tsk j &&
                 task_is_scheduled job_task sched j t)
              ts = num_cpus.
        Proof.
          rename H_all_jobs_from_taskset into FROMTS,
                 H_no_parallelism into SEQUENTIAL,
                 H_no_intra_task_parallelism into NOINTRA,
                 H_invariant_holds into INV.
          unfold JLFP_JLDP_scheduling_invariant_holds in *.
          intros j tsk t JOBtsk BACK.
          rewrite <- INV with (j := j) (t := t); last by done.
 
          assert (EQ:  (preim (fun j0 : JobIn arr_seq => job_task j0)
             (fun j0 : sporadic_task =>
              is_interfering_task_jlfp tsk j0 &&
                                       task_is_scheduled job_task sched j0 t)) =1 (fun j0 => higher_eq_priority t j0 j && (j0 \in jobs_scheduled_at sched t))).
          {
            red; intro j'; unfold preim; simpl.
            destruct (j' \in jobs_scheduled_at sched t) eqn:SCHED'.
            {
              rewrite SCHED'.
              destruct (higher_eq_priority t j' j) eqn:HP'.
              {
                rewrite andbT; apply/andP; split.
                {
                  unfold is_interfering_task_jlfp; apply/eqP; red; intro BUG.
                  subst tsk.
                  (* This requires further assumptions. *)
                  admit.
                }
                {
                  unfold jobs_scheduled_at in *.
                  apply mem_bigcat_ord_exists in SCHED'; des.
                  apply/exists_inP; exists i; first by done.
                  unfold schedules_job_of_tsk, make_sequence in *.
                  destruct (sched i t); last by done.
                  by rewrite mem_seq1 in SCHED'; move: SCHED' => /eqP EQj; subst.
                }
              }
              {
                exfalso; apply negbT in HP'; move: HP' => /negP HP'; apply HP'.
                apply interfering_job_has_higher_eq_prio; first by done.
                apply mem_bigcat_ord_exists in SCHED'; des.
                unfold scheduled, jobs_scheduled_at, make_sequence in *.
                apply/exists_inP; exists i; first by done.
                destruct (sched i t); last by done.
                by rewrite mem_seq1 in SCHED'; move: SCHED' => /eqP EQj; subst. 
              }   
            }
            {
              destruct (is_interfering_task_jlfp tsk (job_task j')) eqn:INTERF'.
              {
                rewrite andTb SCHED' andbF.
                admit. (* This requires further assumptions. *)
              }
              {
                by rewrite SCHED' andbF andFb.
              }
            }
          }
           
          rewrite -[count _ (jobs_scheduled_at _ _)]size_filter.
          assert (SUBST: [seq j_other <- jobs_scheduled_at sched t | higher_eq_priority t j_other j] = [seq j_other <- jobs_scheduled_at sched t | higher_eq_priority t j_other j && (j_other \in jobs_scheduled_at sched t)]).
          {
            by apply eq_in_filter; red; intros x IN; rewrite IN andbT.
          }
          rewrite SUBST; clear SUBST.
          rewrite size_filter.
          rewrite -(eq_count EQ).
          rewrite -[count _ (jobs_scheduled_at _ _)]count_filter.
          rewrite -count_filter.
          rewrite -[count _ [seq _ <- jobs_scheduled_at _ _ | _]]count_map.
          apply/perm_eqP.
          apply uniq_perm_eq; first by apply filter_uniq.
          {
            rewrite map_inj_in_uniq;
              first by apply filter_uniq; apply scheduled_jobs_unique.
            unfold jobs_of_same_task_dont_execute_in_parallel in NOINTRA.
            red; intros x y INx INy EQtask.
            apply NOINTRA with (t := t); try (by done).
            {
              rewrite mem_filter in INx; move: INx => /andP [_ SCHEDx].
              apply mem_bigcat_ord_exists in SCHEDx; destruct SCHEDx as [cpu SCHEDx].
              apply/existsP; exists cpu; apply/andP; split; first by done.
              by unfold make_sequence in SCHEDx; destruct (sched cpu t);
                [ by rewrite mem_seq1 eq_sym in SCHEDx; apply/eqP; f_equal; apply/eqP
                | by rewrite in_nil in SCHEDx].
            }
            {
              rewrite mem_filter in INy; move: INy => /andP [_ SCHEDy].
              apply mem_bigcat_ord_exists in SCHEDy; destruct SCHEDy as [cpu SCHEDy].
              apply/existsP; exists cpu; apply/andP; split; first by done.
              by unfold make_sequence in SCHEDy; destruct (sched cpu t);
                [ by rewrite mem_seq1 eq_sym in SCHEDy; apply/eqP; f_equal; apply/eqP
                | by rewrite in_nil in SCHEDy].
            }
          }
          {
            red; intro x; apply/idP/idP.
            {
              unfold task_is_scheduled in *.
              intros IN; rewrite mem_filter in IN; move: IN => /andP [/exists_inP SCHED IN].
              destruct SCHED as [cpu INcpu SCHED].
              generalize SCHED; intro SCHEDjob.
              unfold schedules_job_of_tsk in SCHEDjob.
              destruct (sched cpu t) as [j'|] eqn:SCHEDj'; last by done.
              move: SCHEDjob => /eqP SCHEDjob; subst x.
              apply/mapP; exists j'; last by done.
              rewrite mem_filter; apply/andP; split;
                first by apply/exists_inP; exists cpu.
              unfold jobs_scheduled_at.
              apply mem_bigcat_ord with (j := cpu); first by apply ltn_ord.
              by unfold make_sequence; rewrite SCHEDj' mem_seq1 eq_refl.
            }
            {
              intros IN; rewrite mem_filter.
              move: IN => /mapP IN; destruct IN as [j' IN]; subst x.
              rewrite mem_filter in IN; move: IN => /andP [SCHEDj' IN].
              apply/andP; split; first by done.
              by apply FROMTS.
            }
          }
        Qed.

      End BasicLemmas.
      
    End JLDP.

  End SchedulingInvariants.
  
End Platform.