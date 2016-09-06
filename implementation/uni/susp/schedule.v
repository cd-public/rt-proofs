Require Import rt.util.all.
Require Import rt.model.job rt.model.arrival_sequence rt.model.priority.
Require Import rt.model.uni.schedule.
Require Import rt.model.uni.susp.platform.
Require Import rt.model.uni.transformation.construction.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat fintype bigop seq path.

Module ConcreteScheduler.

  Import Job ArrivalSequence UniprocessorSchedule PlatformWithSuspensions Priority
         ScheduleConstruction.

  (* In this section, we implement a priority-based uniprocessor scheduler *)
  Section Implementation.
    
    Context {Job: eqType}.
    Variable job_cost: Job -> time.

    (* Let arr_seq be any job arrival sequence...*)
    Variable arr_seq: arrival_sequence Job.

    (* ...that is subject to job suspensions. *)
    Variable next_suspension: job_suspension Job.
    
    (* Also, assume that a JLDP policy is given. *)
    Variable higher_eq_priority: JLDP_policy arr_seq.

    (* Next, we show how to recursively construct the schedule. *)
    Section ScheduleConstruction.

      (* For any time t, suppose that we have generated the schedule prefix in the
         interval [0, t). Then, we must define what should be scheduled at time t. *)
      Variable sched_prefix: schedule arr_seq.
      Variable t: time.
      
      (* For simplicity, let's use some local names. *)
      Let is_pending := pending job_cost sched_prefix.
      Let is_suspended :=
        suspended_at job_cost next_suspension sched_prefix.

      (* Consider the list of pending, non-suspended jobs at time t. *)
      Definition pending_jobs :=
        [seq j <- jobs_arrived_up_to arr_seq t | is_pending j t && ~~ is_suspended j t].
        
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
      intros j IN; apply JobIn_arrived in IN.
      rewrite /arrived_before ltnS in IN.
      rewrite /pending /has_arrived IN 2!andTb.
      have COMP: completed_by job_cost sched1 j t =
                 completed_by job_cost sched2 j t.
      {
        rewrite /completed_by.
        rewrite /completed_by; f_equal.
        apply eq_big_nat; move => i /= LTi.
        by rewrite /service_at /scheduled_at ALL.
      }
      rewrite COMP; do 2 f_equal.
      rewrite /suspended_at; f_equal; first by rewrite COMP.
      have EX: [exists t0: 'I_t, scheduled_at sched1 j t0] =
               [exists t0: 'I_t, scheduled_at sched2 j t0].
      {
        apply/idP/idP.
        {
          move => /existsP [t0 SCHED].
          by apply/existsP; exists t0; rewrite /scheduled_at -ALL.
        }
        {
          move => /existsP [t0 SCHED].
          by apply/existsP; exists t0; rewrite /scheduled_at ALL.
        }
      }
      have BEG: time_after_last_execution sched1 j t =
                time_after_last_execution sched2 j t.
      {
        rewrite /time_after_last_execution EX.
        case: ifP => _; last by done.
        f_equal; apply eq_bigl.
        by intros t0; rewrite /scheduled_at ALL.
      }
      have SUSP: suspension_duration next_suspension sched1 j t =
                 suspension_duration next_suspension sched2 j t.
      {
        rewrite /suspension_duration BEG; f_equal.
        rewrite /service /service_during big_nat_cond [in RHS]big_nat_cond.
        apply congr_big; try (by done).
        move => i /= /andP [LTi _].
        rewrite /service_at /scheduled_at ALL //.
        apply: (leq_trans LTi).
        by apply last_execution_bounded_by_identity.
      }
      by rewrite BEG SUSP.
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

    (* Let arr_seq be any job arrival sequence with no duplicates... *)
    Variable arr_seq: arrival_sequence Job.
    Hypothesis H_arrival_sequence_is_a_set: arrival_sequence_is_a_set arr_seq.

    (* ...that is subject to suspension times. *)
    Variable next_suspension: job_suspension Job.

    (* Consider any JLDP policy that is reflexive, transitive and total. *)
    Variable higher_eq_priority: JLDP_policy arr_seq.
    Hypothesis H_priority_is_reflexive: JLDP_is_reflexive higher_eq_priority.
    Hypothesis H_priority_is_transitive: JLDP_is_transitive higher_eq_priority. 
    Hypothesis H_priority_is_total: JLDP_is_total higher_eq_priority. 

    (* Let sched denote our concrete scheduler implementation. *)
    Let sched := scheduler job_cost arr_seq next_suspension higher_eq_priority.

    (* To conclude, we prove the important properties of the scheduler implementation. *)
    
    (* First, we show that jobs do not execute before they arrive...*)
    Theorem scheduler_jobs_must_arrive_to_execute:
      jobs_must_arrive_to_execute sched.
    Proof.
      unfold jobs_must_arrive_to_execute.
      move => j t /eqP SCHED.
      rewrite /sched scheduler_uses_construction_function in SCHED.
      rewrite /highest_priority_job in SCHED.
      set jobs := sorted_jobs _ _ _ _ _ _ in SCHED.
      suff IN: j \in jobs.
      {
        rewrite mem_sort mem_filter in IN.
        by move: IN => /andP [/andP [/andP [ARR _] _] _].
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
        move: IN => /andP [/andP [/andP [_ NOTCOMP] _] _].
        by rewrite /completed_by -/sched EQ eq_refl in NOTCOMP.
      }
      destruct jobs; first by done.
      by case: HP => SAME; subst; rewrite in_cons eq_refl.
    Qed.

    (* In addition, the scheduler is work conserving, ... *)
    Theorem scheduler_work_conserving:
      work_conserving job_cost next_suspension sched. 
    Proof.
      intros j t BACK.
      move: BACK => /andP [/andP [/andP [ARR NOTCOMP] NOTSCHED] NOTSUSP].
      rewrite /scheduled_at /sched scheduler_uses_construction_function in NOTSCHED.
      rewrite /scheduled_at /sched scheduler_uses_construction_function.
      case HP: (highest_priority_job _ _ _ _ _ ) => [j_hp|];
        first by exists j_hp.
      rewrite /highest_priority_job in HP.
      set jobs := sorted_jobs _ _ _ _ _ _ in HP.
      suff IN: j \in jobs by destruct jobs.
      by rewrite mem_sort mem_filter /pending ARR NOTCOMP NOTSUSP /=; apply JobIn_arrived.
    Qed.

    (* ... respects the JLDP policy..., *)
    Theorem scheduler_respects_policy :
      respects_JLDP_policy job_cost next_suspension sched higher_eq_priority.
    Proof.
      rename H_priority_is_transitive into TRANS, H_priority_is_total into TOTAL.
      move => j1 j2 t BACK /eqP SCHED.
      move: BACK => /andP [/andP [/andP [ARR NOTCOMP] NOTSCHED] NOTSUSP].
      rewrite /scheduled_at /sched scheduler_uses_construction_function in NOTSCHED.
      rewrite /scheduled_at /sched scheduler_uses_construction_function in SCHED.
      rewrite /highest_priority_job in SCHED NOTSCHED.
      set jobs := sorted_jobs _ _ _ _ _ _ in SCHED NOTSCHED.
      have IN: j1 \in jobs.
        by rewrite mem_sort mem_filter /pending ARR NOTCOMP NOTSUSP /=; apply JobIn_arrived.
      have SORT: sorted (higher_eq_priority t) jobs by apply sort_sorted.
      destruct jobs as [|j0 l]; first by done.
      rewrite in_cons in IN; move: IN => /orP [/eqP EQ | IN];
        first by subst; rewrite /= eq_refl in NOTSCHED.
      case: SCHED => SAME; subst.
      simpl in SORT; apply order_path_min in SORT; last by done.
      by move: SORT => /allP ALL; apply ALL.
    Qed.

    (* ... and respects self-suspensions. *)
    Theorem scheduler_respects_self_suspensions:
      respects_self_suspensions job_cost next_suspension sched.
    Proof.
      move => j t /eqP SCHED.
      rewrite /scheduled_at /sched scheduler_uses_construction_function in SCHED.
      rewrite /highest_priority_job in SCHED.
      set jobs := sorted_jobs _ _ _ _ _ _ in SCHED.
      have IN: j \in jobs.
      {
        destruct jobs; first by done.
        by case: SCHED => SAME; subst; rewrite in_cons eq_refl.
      }
      rewrite mem_sort mem_filter in IN.
      by move: IN => /andP [/andP [_ NOTSUSP] _]; apply/negP.
    Qed.
    
  End Proofs.
    
End ConcreteScheduler.