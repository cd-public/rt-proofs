Require Import rt.util.all.
Require Import rt.model.arrival.basic.job rt.model.arrival.basic.arrival_sequence rt.model.priority.
Require Import rt.model.schedule.uni.jitter.schedule
               rt.model.schedule.uni.jitter.platform.
Require Import rt.model.schedule.uni.transformation.construction.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat fintype bigop seq path.

Module ConcreteScheduler.

  Import Job ArrivalSequence UniprocessorScheduleWithJitter Platform Priority
         ScheduleConstruction.

  (* In this section, we implement a jitter-aware priority-based uniprocessor scheduler *)
  Section Implementation.
    
    Context {Job: eqType}.
    Variable job_cost: Job -> time.
    Variable job_jitter: Job -> time.

    (* Let arr_seq be any job arrival sequence. *)
    Variable arr_seq: arrival_sequence Job.
    
    (* Also, assume that a JLDP policy is given. *)
    Variable higher_eq_priority: JLDP_policy arr_seq.

    (* Next, we show how to recursively construct the schedule. *)
    Section ScheduleConstruction.

      (* For any time t, suppose that we have generated the schedule prefix in the
         interval [0, t). Then, we must define what should be scheduled at time t. *)
      Variable sched_prefix: schedule arr_seq.
      Variable t: time.
      
      (* For simplicity, let's use some local names. *)
      Let is_pending := pending job_cost job_jitter sched_prefix.

      (* Consider the list of pending jobs at time t. *)
      Definition pending_jobs :=
        [seq j <- actual_arrivals_up_to job_jitter arr_seq t | is_pending j t].
        
      (* Then, we sort this list by priority... *)
      Definition sorted_jobs := sort (higher_eq_priority t) pending_jobs.

      (* ...and pick the highest-priority job. *)
      Definition highest_priority_job := ohead sorted_jobs.

    End ScheduleConstruction.

    (* Starting from the empty schedule, the final schedule is obtained by iteratively
       picking the highest-priority job. *)
    Let empty_schedule : schedule arr_seq := fun t => None.
    Definition scheduler :=
      build_schedule_from_prefixes arr_seq highest_priority_job empty_schedule.

    (* Then, by showing that the construction function depends only on the prefix, ... *)
    Lemma scheduler_depends_only_on_prefix:
      forall sched1 sched2 t,
        (forall t0, t0 < t -> sched1 t0 = sched2 t0) ->
        highest_priority_job sched1 t = highest_priority_job sched2 t.
    Proof.
      intros sched1 sched2 t ALL.
      rewrite /highest_priority_job /sorted_jobs.
      suff SAME: pending_jobs sched1 t = pending_jobs sched2 t by rewrite SAME.
      apply eq_in_filter.
      intros j IN; rewrite mem_filter in IN.
      move: IN => /andP [ARR IN].
      rewrite ltnS in ARR.
      rewrite /pending /jitter_has_passed ARR 2!andTb; f_equal.
      rewrite /completed_by; f_equal.
      apply eq_big_nat; move => i /= LTi.
      by rewrite /service_at /scheduled_at ALL.
    Qed.
      
    (* ...we infer that the generated schedule is indeed based on the construction function. *)
    Corollary scheduler_uses_construction_function:
      forall t, scheduler t = highest_priority_job scheduler t.
    Proof.
      by ins; apply prefix_dependent_schedule_construction,
                    scheduler_depends_only_on_prefix.
    Qed.
    
  End Implementation.

  (* In this section, we prove the properties of the scheduler that are used
     as hypotheses in the analyses. *)
  Section Proofs.

    Context {Job: eqType}.
    Variable job_cost: Job -> time.
    Variable job_jitter: Job -> time.

    (* Let arr_seq be any job arrival sequence with no duplicates. *)
    Variable arr_seq: arrival_sequence Job.
    Hypothesis H_arrival_sequence_is_a_set: arrival_sequence_is_a_set arr_seq.

    (* Consider any JLDP policy that is reflexive, transitive and total. *)
    Variable higher_eq_priority: JLDP_policy arr_seq.
    Hypothesis H_priority_is_reflexive: JLDP_is_reflexive higher_eq_priority.
    Hypothesis H_priority_is_transitive: JLDP_is_transitive higher_eq_priority. 
    Hypothesis H_priority_is_total: JLDP_is_total higher_eq_priority. 

    (* Let sched denote our concrete scheduler implementation. *)
    Let sched := scheduler job_cost job_jitter arr_seq higher_eq_priority.

    (* To conclude, we prove the important properties of the scheduler implementation. *)
    
    (* First, we show that jobs only execute after the jitter has passed... *)
    Theorem scheduler_jobs_execute_after_jitter:
      jobs_execute_after_jitter job_jitter sched.
    Proof.
      move => j t /eqP SCHED.
      rewrite /sched scheduler_uses_construction_function in SCHED.
      rewrite /highest_priority_job in SCHED.
      set jobs := sorted_jobs _ _ _ _ _ _ in SCHED.
      suff IN: j \in jobs.
      {
        rewrite mem_sort mem_filter in IN.
        by move: IN => /andP [/andP [ARR _] _].
      }
      destruct jobs; first by done.
      by case: SCHED => SAME; subst; rewrite in_cons eq_refl.
    Qed.

    (* ... nor after completion. *)
    Theorem scheduler_completed_jobs_dont_execute:
      completed_jobs_dont_execute job_cost sched.
    Proof.
      intros j t.
      induction t;
        first by rewrite /service /service_during big_geq //.
      rewrite /service /service_during big_nat_recr //=.
      rewrite leq_eqVlt in IHt; move: IHt => /orP [/eqP EQ | LT]; last first.
      {
        apply: leq_trans LT; rewrite -addn1.
          by apply leq_add; last by apply leq_b1.
      }
      rewrite -[job_cost _]addn0; apply leq_add; first by rewrite -EQ.
      rewrite leqn0 eqb0 /scheduled_at.
      rewrite /sched scheduler_uses_construction_function.
      rewrite /highest_priority_job.
      apply/eqP; intro HP.
      set jobs := sorted_jobs _ _ _ _ _ _ in HP.
      suff IN: j \in jobs.
      {
        rewrite mem_sort mem_filter in IN.
        move: IN => /andP [/andP [_ NOTCOMP] _].
        by rewrite /completed_by -/sched EQ eq_refl in NOTCOMP.
      }
      destruct jobs; first by done.
      by case: HP => SAME; subst; rewrite in_cons eq_refl.
    Qed.

    (* In addition, the scheduler is work conserving... *)
    Theorem scheduler_work_conserving:
      work_conserving job_cost job_jitter sched. 
    Proof.
      intros j t BACK.
      move: BACK => /andP [/andP [ARR NOTCOMP] NOTSCHED].
      rewrite /scheduled_at /sched scheduler_uses_construction_function in NOTSCHED.
      rewrite /scheduled_at /sched scheduler_uses_construction_function.
      case HP: (highest_priority_job _ _ _ _ _ ) => [j_hp|];
        first by exists j_hp.
      rewrite /highest_priority_job in HP.
      set jobs := sorted_jobs _ _ _ _ _ _ in HP.
      suff IN: j \in jobs by destruct jobs.
      by rewrite mem_sort mem_filter /pending ARR NOTCOMP /=; apply actual_arrivals_arrived.
    Qed.

    (* ... and respects the JLDP policy. *)
    Theorem scheduler_respects_policy :
      respects_JLDP_policy job_cost job_jitter sched higher_eq_priority.
    Proof.
      rename H_priority_is_transitive into TRANS, H_priority_is_total into TOTAL.
      move => j1 j2 t BACK /eqP SCHED.
      move: BACK => /andP [/andP [ARR NOTCOMP] NOTSCHED].
      rewrite /scheduled_at /sched scheduler_uses_construction_function in NOTSCHED.
      rewrite /scheduled_at /sched scheduler_uses_construction_function in SCHED.
      rewrite /highest_priority_job in SCHED NOTSCHED.
      set jobs := sorted_jobs _ _ _ _ _ _ in SCHED NOTSCHED.
      have IN: j1 \in jobs.
        by rewrite mem_sort mem_filter /pending ARR NOTCOMP /=; apply actual_arrivals_arrived.
      have SORT: sorted (higher_eq_priority t) jobs by apply sort_sorted.
      destruct jobs as [|j0 l]; first by done.
      rewrite in_cons in IN; move: IN => /orP [/eqP EQ | IN];
        first by subst; rewrite /= eq_refl in NOTSCHED.
      case: SCHED => SAME; subst.
      simpl in SORT; apply order_path_min in SORT; last by done.
      by move: SORT => /allP ALL; apply ALL.
    Qed.

  End Proofs.
    
End ConcreteScheduler.