Require Import rt.util.all.
Require Import rt.model.job rt.model.arrival_sequence rt.model.priority.
Require Import rt.model.uni.schedule.
Require Import rt.model.uni.basic.platform.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat fintype bigop seq path.

Module ConcreteScheduler.

  Import Job ArrivalSequence UniprocessorSchedule Platform Priority.

  (* In this section, we implement a priority-based uniprocessor scheduler *)
  Section Implementation.
    
    Context {Job: eqType}.
    Variable job_cost: Job -> time.

    (* Let arr_seq be any arrival sequence.*)
    Variable arr_seq: arrival_sequence Job.

    (* Assume a JLDP policy is given. *)
    Variable higher_eq_priority: JLDP_policy arr_seq.

    (* Consider the list of pending jobs at time t. *)
    Definition jobs_pending_at (sched: schedule arr_seq) (t: time) :=
      [seq j <- jobs_arrived_up_to arr_seq t | pending job_cost sched j t].

    (* First, we sort this list by priority. *)
    Definition sorted_pending_jobs (sched: schedule arr_seq) (t: time) :=
      sort (higher_eq_priority t) (jobs_pending_at sched t).

    (* Then, starting from the empty schedule as a base, ... *)
    Definition empty_schedule : schedule arr_seq :=
      fun t => None.

    (* ..., we redefine the mapping of jobs to processors at any time t as follows.
       The job to be scheduled is either the head of the sorted list or None, in case
       there is no pending job. *)
    Definition update_schedule (prev_sched: schedule arr_seq)
                               (t_next: time) : schedule arr_seq :=
      fun t =>
        if t == t_next then
          ohead (sorted_pending_jobs prev_sched t) (* head of the list, if it exists *)
        else prev_sched t.

    (* The schedule is iteratively constructed by applying assign_jobs at every time t. *)
    Fixpoint schedule_prefix (t_max: time) : schedule arr_seq := 
      if t_max is t_prev.+1 then
        (* At time t_prev + 1, schedule jobs that have not completed by time t_prev. *)
        update_schedule (schedule_prefix t_prev) t_prev.+1
      else
        (* At time 0, schedule any jobs that arrive. *)
        update_schedule empty_schedule 0.

    (* This iteration yields the following scheduler implementation. *)
    Definition scheduler (t: time) := (schedule_prefix t) t.

  End Implementation.

  (* In this section, we prove the properties of the scheduler that are used
     as hypotheses in the analyses. *)
  Section Proofs.

    Context {Job: eqType}.
    Variable job_cost: Job -> time.

    (* Let arr_seq be any job arrival sequence with no duplicates. *)
    Variable arr_seq: arrival_sequence Job.
    Hypothesis H_arrival_sequence_is_a_set: arrival_sequence_is_a_set arr_seq.

    (* Consider any JLDP policy that is transitive and total. *)
    Variable higher_eq_priority: JLDP_policy arr_seq.
    Hypothesis H_priority_transitive: forall t, transitive (higher_eq_priority t).
    Hypothesis H_priority_total: forall t, total (higher_eq_priority t).

    (* Let sched denote our concrete scheduler implementation. *)
    Let sched := scheduler job_cost arr_seq higher_eq_priority.

    (* Next, we prove some helper lemmas about the scheduler construction. *)
    Section HelperLemmas.

      (* Let's use a shorter name for the schedule prefix function. *)
      Let sched_prefix := schedule_prefix job_cost arr_seq higher_eq_priority.
      
      (* First, we show that the scheduler preserves its prefixes. *)
      Lemma scheduler_same_prefix :
        forall t t_max,
          t <= t_max ->
          sched_prefix t_max t = sched t.
      Proof.
        intros t t_max LEt.
        induction t_max.
        {
          by rewrite leqn0 in LEt; move: LEt => /eqP EQ; subst.
        }
        {
          rewrite leq_eqVlt in LEt.
          move: LEt => /orP [/eqP EQ | LESS]; first by subst.
          {
            feed IHt_max; first by done.
            unfold sched_prefix, schedule_prefix, update_schedule at 1.
            assert (FALSE: t == t_max.+1 = false).
            {
              by apply negbTE; rewrite neq_ltn LESS orTb.
            } rewrite FALSE.
            by rewrite -IHt_max.
          }
        }
      Qed.

      (* Moreover, given the sorted list of pending jobs, ...*)
      Let sorted_jobs (t: time) :=
        sorted_pending_jobs job_cost arr_seq higher_eq_priority sched t.

      (* ..., we prove that the scheduler always picks the first job of the list. *)
      Lemma scheduler_picks_first_job:
        forall t,
          sched t = ohead (sorted_jobs t).
      Proof.
        unfold sched, scheduler, schedule_prefix in *.
        destruct t.
        {
          rewrite /update_schedule eq_refl; f_equal.
          unfold sorted_jobs, sorted_pending_jobs; f_equal.
          unfold jobs_pending_at; apply eq_filter; red; intro j'.
          unfold pending; f_equal; f_equal.
          unfold completed_by, service, service_during.
          by rewrite big_geq // big_geq //.
        }
        {
          rewrite {1}/update_schedule eq_refl; f_equal.
          unfold sorted_jobs, sorted_pending_jobs; f_equal.
          unfold jobs_pending_at; apply eq_filter; red; intro j'.
          unfold pending; f_equal; f_equal.
          unfold completed_by, service, service_during; f_equal.
          apply eq_big_nat; move => t0 /andP [_ LT].
          unfold service_at, scheduled_at. 
          fold (schedule_prefix job_cost arr_seq higher_eq_priority).
          have SAME := scheduler_same_prefix.
          unfold sched_prefix, sched in *.
          by rewrite /schedule_prefix SAME.
        }
      Qed.

    End HelperLemmas.

    (* To conclude, we prove the important properties of the scheduler implementation. *)
    
    (* First, we show that jobs do not execute before they arrive...*)
    Theorem scheduler_jobs_must_arrive_to_execute:
      jobs_must_arrive_to_execute sched.
    Proof.
      unfold jobs_must_arrive_to_execute.
      intros j t SCHED.
      unfold sched, scheduled_at, scheduler, schedule_prefix in SCHED.
      destruct t.
      {
        rewrite /update_schedule eq_refl in SCHED.
        set jobs := sorted_pending_jobs _ _ _ _ _ in SCHED.
        suff IN: j \in jobs.
        {
          rewrite mem_sort mem_filter in IN; move: IN => /andP [_ ARR].
          by apply JobIn_arrived in ARR.
        }
        case SORT: jobs => [| j0 l /=]; first by rewrite SORT /= in SCHED.
        rewrite SORT /= in SCHED.
        move: SCHED; move/eqP; case; intro EQ; subst.
        by rewrite in_cons eq_refl orTb.
      }
      {
        rewrite /update_schedule eq_refl in SCHED.
        set jobs := sorted_pending_jobs _ _ _ _ _ in SCHED.
        suff IN: j \in jobs.
        {
          rewrite mem_sort mem_filter in IN; move: IN => /andP [_ ARR].
          by apply JobIn_arrived in ARR.
        }
        case SORT: jobs => [| j0 l /=]; first by rewrite SORT /= in SCHED.
        rewrite SORT /= in SCHED.
        move: SCHED; move/eqP; case; intro EQ; subst.
        by rewrite in_cons eq_refl orTb.
      }
    Qed.

    (* ... nor after completion. *)
    Theorem scheduler_completed_jobs_dont_execute:
      completed_jobs_dont_execute job_cost sched.
    Proof.
      unfold completed_jobs_dont_execute, service, service_during.
      intros j t.
      induction t; first by rewrite big_geq.
      {
        rewrite big_nat_recr // /=.
        rewrite leq_eqVlt in IHt; move: IHt => /orP [/eqP EQ | LESS]; last first.
        {
          destruct (job_cost j); first by rewrite ltn0 in LESS.
          rewrite -addn1; rewrite ltnS in LESS.
          by apply leq_add; last by apply leq_b1.
        }
        rewrite EQ -{2}[job_cost j]addn0; apply leq_add; first by done.
        destruct t.
        {
          rewrite /service_at /scheduled_at.
          destruct (sched 0 == Some j) eqn:SCHED; last by done.
          move: SCHED => /eqP SCHED.
          rewrite scheduler_picks_first_job in SCHED.
          set jobs := sorted_pending_jobs _ _ _ _ _ in SCHED.
          have IN: j \in jobs.
            by destruct jobs; last by move: SCHED => /=; case => SAME; subst; rewrite in_cons eq_refl.
          rewrite mem_sort mem_filter in IN; move: IN => /andP [/andP [_ NOTCOMP] _].
          by rewrite /completed_by -EQ eq_refl in NOTCOMP. 
        }
        {
          unfold service_at, scheduled_at.
          rewrite leqn0 eqb0; apply/eqP; intro SCHED.
          unfold sched, scheduler, schedule_prefix, update_schedule at 1 in SCHED.
          rewrite eq_refl in SCHED.
          set jobs := sorted_pending_jobs _ _ _ _ _ in SCHED.
          have IN: j \in jobs.
            by destruct jobs; last by move: SCHED => /=; case => SAME; subst; rewrite in_cons eq_refl.
          rewrite mem_sort mem_filter in IN; move: IN => /andP [/andP [_ /negP NOTCOMP] _].
          apply NOTCOMP.
          rewrite /completed_by /service /service_during -EQ.
          apply/eqP.
          rewrite big_nat_cond [in RHS]big_nat_cond.
          apply eq_bigr; move => i /andP [/andP [_ LT] _].
          rewrite /service_at /scheduled_at /sched /scheduler.
          fold (schedule_prefix job_cost arr_seq higher_eq_priority).
          by rewrite scheduler_same_prefix.
        }
      }
    Qed.

    (* In addition, the scheduler is work conserving ... *)
    Theorem scheduler_work_conserving:
      work_conserving job_cost sched.
    Proof.
      unfold work_conserving; intros j t BACK.
      set jobs := sorted_pending_jobs job_cost arr_seq higher_eq_priority sched t.
      destruct (sched t) eqn:SCHED; first by exists j0; apply/eqP.
      rewrite scheduler_picks_first_job -/jobs in SCHED.
      destruct jobs eqn:EMPTY; [clear SCHED | by done].
      suff IN: j \in jobs by rewrite EMPTY in_nil in IN.
      move: BACK => /andP [PEND _].
      rewrite mem_sort mem_filter PEND andTb.
      by apply JobIn_arrived; move: PEND => /andP [ARR _].
    Qed.

    (* ... and respects the JLDP policy. *)
    Theorem scheduler_respects_policy :
      respects_JLDP_policy job_cost sched higher_eq_priority.
    Proof.
      unfold respects_JLDP_policy; move => j j_hp t BACK /eqP SCHED.
      move: (SCHED) => OHEAD.
      rewrite scheduler_picks_first_job in OHEAD.
      set jobs := sorted_pending_jobs job_cost arr_seq higher_eq_priority sched t in OHEAD.
      have SORT: sorted (higher_eq_priority t) jobs by apply sort_sorted.
      have IN: j \in jobs.
      {
        rewrite mem_sort mem_filter.
        move: BACK => /andP [PEND _]; rewrite PEND andTb.
        by move: PEND => /andP [ARR _]; apply JobIn_arrived.
      }
      destruct jobs as [|j0 l] eqn:JOBS; first by done.
      move: OHEAD => /=; case => EQ; subst.
      move: IN; rewrite in_cons => /orP [/eqP SAME | OTHER];
        first by move:BACK => /andP [_ /eqP NOTSCHED]; rewrite /scheduled_at SCHED SAME in NOTSCHED.
      suff ALL: all (higher_eq_priority t j_hp) l by move: ALL => /allP ALL; apply ALL.
      by apply order_path_min.
    Qed.

  End Proofs.
    
End ConcreteScheduler.