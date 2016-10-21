Require Import rt.util.all.
Require Import rt.model.arrival.basic.task rt.model.arrival.basic.job rt.model.arrival.basic.arrival_sequence
               rt.model.priority rt.model.arrival.basic.task_arrival.
Require Import rt.model.schedule.uni.jitter.schedule rt.model.schedule.uni.jitter.platform
               rt.model.schedule.uni.jitter.service rt.model.schedule.uni.jitter.workload.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

(* In this file, we provide definitions and lemmas about busy intervals
   and their relation with response times. *)
Module BusyInterval.

  Import Job UniprocessorScheduleWithJitter Priority Platform
         Service Workload TaskArrival.

  (* In this section, we define the notion of a busy interval. *)
  Section Defs.

    Context {Task: eqType}.   
    Context {Job: eqType}.
    Variable job_cost: Job -> time.
    Variable job_jitter: Job -> time.
    Variable job_task: Job -> Task.

    (* Consider any uniprocessor schedule ... *)
    Context {arr_seq: arrival_sequence Job}.
    Variable sched: schedule arr_seq.

    (* ...subject to a JLFP policy. *)
    Variable higher_eq_priority: JLFP_policy arr_seq.
    
    (* Let j be any job to be analyzed. *)
    Variable j: JobIn arr_seq.

    (* For simplicity, let's define some local names. *)
    Let job_pending_at := pending job_cost job_jitter sched.
    Let job_scheduled_at := scheduled_at sched.
    Let job_completed_by := completed_by job_cost sched.
    Let actual_job_arrival (j: JobIn arr_seq) := actual_arrival job_jitter j.
    
    (* We say that t is a quiet time for j iff every higher-priority job that
       has an actual arrival time (with jitter) before t has completed by that time. *)
    Definition quiet_time (t: time) :=
      forall (j_hp: JobIn arr_seq),
        higher_eq_priority j_hp j ->
        actual_arrival_before job_jitter j_hp t ->
        job_completed_by j_hp t.

    (* Based on the definition of quiet time, we say that interval
       [t1, t_busy) is a (potentially unbounded) busy-interval prefix
       iff the interval starts with a quiet time and remains non-quiet. *)
    Definition busy_interval_prefix (t1 t_busy: time) :=
      t1 < t_busy /\
      quiet_time t1 /\
      (forall t, t1 < t < t_busy -> ~ quiet_time t).

    (* Next, we say that an interval [t1, t2) is a busy interval iff
       [t1, t2) is a busy-interval prefix and t2 is a quiet time. *)
    Definition busy_interval (t1 t2: time) :=
      busy_interval_prefix t1 t2 /\
      quiet_time t2.

    (* Now we prove some lemmas about busy intervals. *)
    Section Lemmas.

      (* Recall the list of jobs with actual arrival time (including jitter) in the
         interval [t1, t2). *)
      Let actual_arrivals t1 t2 := actual_arrivals_between job_jitter arr_seq t1 t2.

      (* We begin by proving basic lemmas about the arrival and
         completion of jobs that are pending during a busy interval. *)
      Section BasicLemmas.

        (* Assume that the priority relation is reflexive. *)
        Hypothesis H_priority_is_reflexive: JLFP_is_reflexive higher_eq_priority.

        (* Consider any busy interval [t1, t2)... *)
        Variable t1 t2: time.
        Hypothesis H_busy_interval: busy_interval t1 t2.

        (* ...and assume that job j is pending during this busy interval. *)
        Variable t: time.
        Hypothesis H_during_interval: t1 <= t < t2.
        Hypothesis H_job_is_pending: job_pending_at j t.

        (* First, we prove that job j completes by the end of the busy interval. *)
        Section CompletesDuringBusyInterval.
         
          Lemma job_completes_within_busy_interval:
            job_completed_by j t2.
          Proof.
            rename H_priority_is_reflexive into REFL, H_busy_interval into BUSY,
                   H_during_interval into INT, H_job_is_pending into PEND.
            move: BUSY => [_ QUIET].
            move: INT => /andP [_ LT2].
            apply QUIET; first by apply REFL.
            apply leq_ltn_trans with (n := t); last by done.
            by move: PEND => /andP [ARR _].
          Qed.

        End CompletesDuringBusyInterval.

        (* Next, we prove that the actual arrival of job j cannot have occurred before the busy interval. *)
        Section ArrivesDuringBusyInterval.

          (* Assume that jobs do not execute after completion. *)
          Hypothesis H_completed_jobs_dont_execute:
            completed_jobs_dont_execute job_cost sched.

          (* Then, we prove that job j's actual arrival (with jitter) occurs no earlier than t1. *)
          Lemma job_arrives_within_busy_interval:
            t1 <= actual_arrival job_jitter j.
          Proof.
            rename H_priority_is_reflexive into REFL, H_busy_interval into BUSY, 
                   H_during_interval into INT, H_job_is_pending into PEND.
            apply contraT; rewrite -ltnNge; intro LT1.
            move: BUSY => [[_ [QUIET _]] _].
            move: PEND => /andP [_ /negP NOTCOMP].
            move: INT => /andP [LE _].
            exfalso; apply NOTCOMP.
            apply completion_monotonic with (t0 := t1); try (by done).
            by apply QUIET; first by apply REFL.
          Qed.

        End ArrivesDuringBusyInterval.

      End BasicLemmas.
      
      (* In this section, we prove that during a busy interval there
         always exists a pending job. *)
      Section ExistsPendingJob.

        (* Assume that jobs do not execute after completion. *)
        Hypothesis H_completed_jobs_dont_execute:
          completed_jobs_dont_execute job_cost sched.

        (* Let [t1, t2] be any interval where time t1 is quiet and
           time t2 is not quiet. *)
        Variable t1 t2: time.
        Hypothesis H_interval: t1 <= t2.
        Hypothesis H_quiet: quiet_time t1.
        Hypothesis H_not_quiet: ~ quiet_time t2.
        
      (* Then, we prove that there exists a job pending at time t2
         that has higher or equal priority (with respect ot tsk). *)
        Lemma not_quiet_implies_exists_pending_job:
          exists (j_hp: JobIn arr_seq),
            actual_arrival_between job_jitter j_hp t1 t2 /\
            higher_eq_priority j_hp j /\
            ~ job_completed_by j_hp t2. 
        Proof.
          rename H_quiet into QUIET, H_not_quiet into NOTQUIET.
          destruct (has (fun j_hp => (~~ job_completed_by j_hp t2) && higher_eq_priority j_hp j)
                        (actual_arrivals t1 t2)) eqn:COMP.
          {
            move: COMP => /hasP [j_hp ARR /andP [NOTCOMP HP]].
            exists j_hp; repeat split; [ | by done | by apply/negP].
            rewrite mem_filter in ARR; move: ARR => /andP [GE ARR].
            apply/andP; split; first by done.
            by apply actual_arrivals_arrived.
          }
          {
            apply negbT in COMP; rewrite -all_predC in COMP.
            move: COMP => /allP COMP.
            exfalso; apply NOTQUIET; intros j_hp HP ARR.
            destruct (ltnP (actual_job_arrival j_hp) t1) as [BEFORE | AFTER];
              first by specialize (QUIET j_hp HP BEFORE); apply completion_monotonic with (t := t1).
            feed (COMP j_hp);
              first by rewrite mem_filter; apply/andP; split; last by apply actual_arrivals_arrived.
            by rewrite /= HP andbT negbK in COMP.
          }
        Qed.

      End ExistsPendingJob.

      (* In this section, we prove that during a busy interval the
         processor is never idle. *)
      Section ProcessorAlwaysBusy.

        (* Assume that the schedule is work-conserving and that jobs do
           not execute before the jitter has passed nor after completion. *)
        Hypothesis H_work_conserving: work_conserving job_cost job_jitter sched.
        Hypothesis H_completed_jobs_dont_execute: completed_jobs_dont_execute job_cost sched.
        Hypothesis H_jobs_execute_after_jitter: jobs_execute_after_jitter job_jitter sched.
        
        (* Consider any interval [t1, t2] such that t1 < t2 and t1 is the only quiet time. *)
        Variable t1 t2: time.
        Hypothesis H_strictly_larger: t1 < t2.
        Hypothesis H_quiet: quiet_time t1. 
        Hypothesis H_not_quiet: forall t, t1 < t <= t2 -> ~ quiet_time t.

        (* We prove that at every time t in [t1, t2], the processor is not idle. *)
        Lemma not_quiet_implies_not_idle:
          forall t,
            t1 <= t <= t2 ->
            ~ is_idle sched t.
        Proof.
          unfold total_service_during, work_conserving in *.
          rename H_not_quiet into NOTQUIET, H_work_conserving into WORK.
          move => t /andP [GEt LEt] /eqP IDLE.
          rewrite leq_eqVlt in GEt; move: GEt => /orP [/eqP EQUAL | LARGER].
          {
            subst t.
            feed (NOTQUIET t1.+1); first by apply/andP; split.
            apply NOTQUIET.
            intros j_hp HP ARR.
            apply completion_monotonic with (t := t1); [by done | by done |].
            apply contraT; intro NOTCOMP.
            destruct (scheduled_at sched j_hp t1) eqn:SCHEDhp;
              first by move: SCHEDhp => /eqP SCHEDhp; rewrite IDLE in SCHEDhp.
            apply negbT in SCHEDhp.
            feed (WORK j_hp t1); first by repeat (apply/andP; split).
            move: WORK => [j_other /eqP SCHEDother].
            by rewrite IDLE in SCHEDother.
          }
          {
            feed (NOTQUIET t); first by apply/andP; split.
            apply NOTQUIET; clear NOTQUIET.
            intros j_hp HP ARR.
            apply contraT; intros NOTCOMP.
            destruct (scheduled_at sched j_hp t) eqn:SCHEDhp;
              first by move: SCHEDhp => /eqP SCHEDhp; rewrite IDLE in SCHEDhp.
            apply negbT in SCHEDhp.
            feed (WORK j_hp t);
              first by repeat (apply/andP; split); first by apply ltnW.
            move: WORK => [j_other /eqP SCHEDother].
            by rewrite IDLE in SCHEDother.
          }
        Qed.

        (* In fact, we can infer a stronger property. *)
        Section OnlyHigherOrEqualPriority.

          (* If the JLFP policy is transitive and is respected by the schedule, ...*)
          Hypothesis H_priority_is_transitive: JLFP_is_transitive higher_eq_priority.
          Hypothesis H_respects_policy:
            respects_JLFP_policy job_cost job_jitter sched higher_eq_priority.

          (* ... then the processor is always busy with a job of higher or equal priority
             and actual arrival time in the interval. *)
          Lemma not_quiet_implies_exists_scheduled_hp_job:
            forall t,
              t1 <= t < t2 ->
              exists j_hp,
                actual_arrival_between job_jitter j_hp t1 t2 /\ 
                higher_eq_priority j_hp j /\
                job_scheduled_at j_hp t.
          Proof.
            have NOTIDLE := not_quiet_implies_not_idle.
            unfold is_idle, FP_is_transitive, transitive in *.
            rename H_not_quiet into NOTQUIET, H_quiet into QUIET, H_priority_is_transitive into TRANS,
                   H_work_conserving into WORK, H_respects_policy into PRIO.
            move => t /andP [GEt LEt].
            feed (NOTIDLE t); first by apply/andP; split; last by apply ltnW.
            destruct (sched t) as [j_hp|] eqn:SCHED; [clear NOTIDLE | by exfalso; apply NOTIDLE].
            move: SCHED => /eqP SCHED.
            exists j_hp.
            have HP: higher_eq_priority j_hp j.
            {
              apply contraT; move => /negP NOTHP; exfalso.
              feed (NOTQUIET t.+1); first by apply/andP; split.
              apply NOTQUIET.
              unfold quiet_time in *; intros j_hp' HP ARR.
              apply contraT; move => /negP NOTCOMP'; exfalso.
              have BACK: backlogged job_cost job_jitter sched j_hp' t.
              {
                apply/andP; split; last first.
                {
                  apply/negP; intro SCHED'.
                  apply only_one_job_scheduled with (j1 := j_hp) in SCHED'; last by done.
                  by subst; rewrite HP in NOTHP.
                }
                apply/andP; split; first by done.
                apply/negP; intro COMP; apply NOTCOMP'.
                by apply completion_monotonic with (t0 := t).
              }
              feed (PRIO j_hp' j_hp t BACK);  first by done.
              by apply NOTHP, TRANS with (y := j_hp').
            }
            repeat split; [| by done | by done].
            {
              move: (SCHED) => PENDING.
              apply scheduled_implies_pending with (job_cost0 := job_cost)
                                             (job_jitter0 := job_jitter) in PENDING; try (by done).
              apply/andP; split;
                last by apply leq_ltn_trans with (n := t); first by move: PENDING => /andP [ARR _].
              apply contraT; rewrite -ltnNge; intro LT; exfalso.
              specialize (QUIET j_hp HP LT).
              have COMP: job_completed_by j_hp t by apply completion_monotonic with (t0 := t1).
              apply completed_implies_not_scheduled in COMP; last by done.
              by move: COMP => /negP COMP; apply COMP.
            }
          Qed.

        End OnlyHigherOrEqualPriority.
        
      End ProcessorAlwaysBusy.

      (* In this section, we show that the length of any busy interval
         is bounded, as long as there is enough supply to accomodate
         the workload of tasks with higher or equal priority. *)
      Section BoundingBusyInterval.

        (* Assume that there are no duplicate job arrivals... *)
        Hypothesis H_arrival_sequence_is_a_set:
          arrival_sequence_is_a_set arr_seq.
        
        (* ...and that jobs do not execute before their arrival or after completion. *)
        Hypothesis H_completed_jobs_dont_execute: completed_jobs_dont_execute job_cost sched.
        Hypothesis H_jobs_execute_after_jitter: jobs_execute_after_jitter job_jitter sched.

        (* Also assume a work-conserving FP schedule, ... *)
        Hypothesis H_work_conserving: work_conserving job_cost job_jitter sched.
        Hypothesis H_respects_policy:
          respects_JLFP_policy job_cost job_jitter sched higher_eq_priority.

        (* ...in which the priority relation is reflexive and transitive. *)
        Hypothesis H_priority_is_reflexive: JLFP_is_reflexive higher_eq_priority.
        Hypothesis H_priority_is_transitive: JLFP_is_transitive higher_eq_priority.
        
        (* Let's recall the notions of service and workload of tasks with higher or equal
           priority (with respect to tsk). *)
        Let actual_hp_service :=
          service_of_higher_or_equal_priority_jobs job_jitter sched higher_eq_priority j.
        Let actual_hp_workload :=
          workload_of_higher_or_equal_priority_jobs job_cost job_jitter arr_seq higher_eq_priority j.

        (* Now we begin the proof. First, we show that the busy interval is bounded. *)
        Section BoundingBusyInterval.

          (* Suppose that job j is pending at time t_busy. *)
          Variable t_busy: time.
          Hypothesis H_j_is_pending: job_pending_at j t_busy.
          
          (* First, we show that there must exist a busy interval prefix. *)
          Section LowerBound.
            
            (* Since job j is pending, there exists a (potentially unbounded)
               busy interval that starts prior to the actual arrival time of j. *)
            Lemma exists_busy_interval_prefix:
              exists t1,
                busy_interval_prefix t1 t_busy.+1 /\
                t1 <= actual_job_arrival j <= t_busy.
            Proof.
              rename H_j_is_pending into PEND, H_respects_policy into PRIO,
                     H_work_conserving into WORK, H_priority_is_reflexive into REFL.
              unfold busy_interval_prefix.
              set dec_quiet :=
                fun t => all
                           (fun (j_hp: JobIn arr_seq) =>
                              higher_eq_priority j_hp j ==> (completed_by job_cost sched j_hp t))
                           (actual_arrivals_before job_jitter arr_seq t).
              destruct ([exists t:'I_t_busy.+1, dec_quiet t]) eqn:EX.
              {
                set last := \max_(t < t_busy.+1 | dec_quiet t) t.
                move: EX => /existsP [t EX].
                have PRED: dec_quiet last by apply (bigmax_pred t_busy.+1 dec_quiet t).
                have QUIET: quiet_time last.
                {
                  move: PRED => /allP PRED.
                  intros j_hp HP ARR; apply actual_arrivals_arrived in ARR.
                  specialize (PRED j_hp ARR).
                  by move: PRED => /implyP PRED; apply PRED.
                }
                exists last.
                split; last first.
                {
                  apply/andP; split; last by move: PEND => /andP [ARR _].
                  apply contraT; rewrite -ltnNge; intros BEFORE.
                  feed (QUIET j); first by apply REFL.
                  specialize (QUIET BEFORE).
                  move: PEND => /andP [_ NOTCOMP].
                  apply completion_monotonic with (t' := t_busy) in QUIET;
                    [by rewrite QUIET in NOTCOMP | by done |].
                  by apply bigmax_ltn_ord with (i0 := t).
                }
                split; first by apply bigmax_ltn_ord with (i0 := t).
                split; first by done.
                {
                  move => t0 /andP [GTlast LTbusy] QUIET0.
                  have PRED0: dec_quiet t0.
                  {
                    apply/allP; intros j_hp ARR; apply/implyP; intros HP.
                    apply actual_arrivals_arrived in ARR.
                    by apply QUIET0.
                  }
                  have BUG: t0 <= last.
                  {
                    have LE := @leq_bigmax_cond _ (fun (x: 'I_t_busy.+1) => dec_quiet x)
                                                (fun x => x) (Ordinal LTbusy) PRED0.
                    by apply LE.
                  }
                  apply leq_trans with (p := last) in GTlast; last by done.
                  by rewrite ltnn in GTlast.
                }
              }
              {
                apply negbT in EX; rewrite negb_exists in EX; move: EX => /forallP ALL.
                exists 0; split;
                  last by apply/andP; split; last by move: PEND => /andP [ARR _].
                split; first by done.
                split; first by intros j_hp _ ARR; rewrite /actual_arrival_before ltn0 in ARR.
                move => t /andP [GE LT].
                specialize (ALL (Ordinal LT)); move: ALL => /negP ALL.
                intros QUIET; apply ALL; simpl.
                apply/allP; intros j_hp ARR; apply/implyP; intros HP.
                apply actual_arrivals_arrived in ARR.
                by apply QUIET.
              }
            Qed.

          End LowerBound.
        
        (* Next we prove that, if there is a point where the requested workload
           is upper-bounded by the supply, then the busy interval eventually ends. *)
          Section UpperBound.

            (* Consider any busy interval that starts at time t1 <= actual_job_arrival j. *)
            Variable t1: time.
            Hypothesis H_is_busy_prefix: busy_interval_prefix t1 t_busy.+1.
            Hypothesis H_busy_prefix_contains_arrival: actual_job_arrival j >= t1.

            (* Next, assume that for some delta > 0, the requested workload
               at time (t1 + delta) is bounded by delta (i.e., the supply). *)
            Variable delta: time.
            Hypothesis H_delta_positive: delta > 0.
            Hypothesis H_workload_is_bounded: actual_hp_workload t1 (t1 + delta) <= delta.

            (* If there exists a quiet time by time (t1 + delta), it trivially follows that
               the busy interval is bounded.
               Thus, let's consider first the harder case where there is no quiet time,
               which turns out to be impossible. *)
            Section CannotBeBusyForSoLong.

              (* Assume that there is no quiet time in the interval (t1, t1 + delta]. *)
              Hypothesis H_no_quiet_time:
                forall t, t1 < t <= t1 + delta -> ~ quiet_time t.

              (* Since the interval is always non-quiet, the processor is always busy
                 with tasks of higher-or-equal priority, i.e., the service done by
                 jobs with actual arrival time in [t1, t1 + delta) equals delta. *)
              Lemma busy_interval_has_uninterrupted_service:
                actual_hp_service t1 (t1 + delta) = delta.
              Proof.
                rename H_is_busy_prefix into PREFIX.
                have EXISTS := not_quiet_implies_exists_scheduled_hp_job.
                feed_n 3 EXISTS; try (by done).
                apply eq_trans with (y := \sum_(t1 <= t < t1 + delta) 1);
                  last by simpl_sum_const; rewrite addKn.
                unfold actual_hp_service, service_of_higher_or_equal_priority_jobs, service_of_jobs.
                rewrite exchange_big /=.
                apply eq_big_nat; move => t /andP [GEt LTt].
                move: PREFIX => [_ [QUIET _]].
                have EX: exists j_hp : JobIn arr_seq,
                           actual_arrival_between job_jitter j_hp t1 (t1 + delta) /\
                           higher_eq_priority j_hp j /\
                           scheduled_at sched j_hp t.
                {
                  apply EXISTS with (t1 := t1) (t2 := t1 + delta); try (by done);
                    last by apply/andP; split.
                  by rewrite -addn1; apply leq_add.
                } clear EXISTS.
                move: EX => [j_hp [/andP [GE LT] [HP SCHED]]].
                rewrite big_mkcond (bigD1_seq j_hp) /=; first last.
                - by rewrite filter_uniq //; apply filter_uniq, JobIn_uniq. 
                - by rewrite mem_filter; apply/andP; split; last by apply actual_arrivals_arrived.
                rewrite HP big1; first by rewrite /service_at SCHED addn0.
                intros j' NEQ; destruct (higher_eq_priority j' j); last by done.
                apply/eqP; rewrite eqb0; apply/negP; move => SCHED'.
                move: NEQ => /eqP NEQ; apply NEQ.
                by apply only_one_job_scheduled with (sched0 := sched) (t0 := t).
              Qed.

              (* Moreover, the fact that the interval is not quiet also implies
                 that there's more workload requested than service received. *)
              Lemma busy_interval_too_much_workload:
                actual_hp_workload t1 (t1 + delta) > actual_hp_service t1 (t1 + delta).
              Proof.
                have PEND := not_quiet_implies_exists_pending_job 
                             H_completed_jobs_dont_execute.
                rename H_no_quiet_time into NOTQUIET, 
                       H_is_busy_prefix into PREFIX, H_respects_policy into PRIO.
                set l := actual_arrivals_between job_jitter arr_seq t1 (t1 + delta).
                set hep := higher_eq_priority.
                unfold actual_hp_service, service_of_higher_or_equal_priority_jobs, service_of_jobs,
                       actual_hp_workload, workload_of_higher_or_equal_priority_jobs, workload_of_jobs.
                fold actual_arrivals l hep.
                move: (PREFIX) => [_ [QUIET _]].
                move: (NOTQUIET) => NOTQUIET'.
                feed (NOTQUIET' (t1 + delta));
                  first by apply/andP; split;
                    first by rewrite -addn1; apply leq_add.
                feed (PEND t1 (t1 + delta)); first by apply leq_addr.
                specialize (PEND QUIET NOTQUIET').
                move: PEND => [j0 [/andP [GE0 LT0] [HP0 NOTCOMP0]]].
                have IN0: j0 \in l.
                  by rewrite mem_filter; apply/andP; split; last by apply actual_arrivals_arrived.
                have UNIQ: uniq l by apply filter_uniq, filter_uniq, JobIn_uniq. 
                rewrite big_mkcond [\sum_(_ <- _ | hep _ _)_]big_mkcond.
                rewrite (bigD1_seq j0); [simpl | by done | by done].
                rewrite (bigD1_seq j0); [simpl | by done | by done].
                rewrite /hep HP0.
                rewrite -add1n addnA [1 + _]addnC addn1.
                apply leq_add; last first.
                {
                  apply leq_sum; intros j1 NEQ.
                  destruct (higher_eq_priority j1 j); last by done.
                  by apply cumulative_service_le_job_cost. 
                }
                rewrite ltn_neqAle; apply/andP; split; last by apply cumulative_service_le_job_cost.
                unfold service_during.
                rewrite (ignore_service_before_jitter job_jitter) //;
                  last by apply/andP; split; last by apply ltnW.
                rewrite <- ignore_service_before_jitter with (t2:=0); rewrite //; [|by apply ltnW].
                by apply/negP.
              Qed.

              (* Using the two lemmas above, we infer that the workload is larger than the
                 interval length. However, this contradicts the assumption H_workload_is_bounded. *)
              Corollary busy_interval_workload_larger_than_interval:
                actual_hp_workload t1 (t1 + delta) > delta.
              Proof.
                rewrite -{1}busy_interval_has_uninterrupted_service.
                by apply busy_interval_too_much_workload.
              Qed.

            End CannotBeBusyForSoLong.

            (* Since the interval cannot remain busy for so long, we prove that
               the busy interval finishes at some point t2 <= t1 + delta. *)
            Lemma busy_interval_is_bounded:
              exists t2,
                t2 <= t1 + delta /\
                busy_interval t1 t2.
            Proof.
              have TOOMUCH := busy_interval_workload_larger_than_interval.
              have BOUNDED := H_workload_is_bounded.
              rename H_is_busy_prefix into PREFIX.

              set dec_quiet :=
                fun t => all
                           (fun (j_hp: JobIn arr_seq) =>
                              higher_eq_priority j_hp j ==> (completed_by job_cost sched j_hp t))
                           (actual_arrivals_before job_jitter arr_seq t).

              destruct ([exists t2:'I_(t1 + delta).+1, (t2 > t1) && dec_quiet t2]) eqn:EX.
              {
                have EX': exists (t2: nat), ((t1 < t2 <= t1 + delta) && dec_quiet t2).
                {
                  move: EX => /existsP [t2 /andP [LE QUIET]].
                  exists t2; apply/andP; split; last by done.
                  by apply/andP; split; last by rewrite -ltnS; apply ltn_ord.
                }
                have MIN := ex_minnP EX'.
                move: MIN => [t2 /andP [/andP [GT LE] QUIET] MIN]; clear EX EX'.
                exists t2; split; first by done.
                split; last first.
                {
                  intros j_hp HP ARR.
                  move: QUIET => /allP QUIET.
                  feed (QUIET j_hp); first by apply actual_arrivals_arrived.
                  by move: QUIET => /implyP QUIET; apply QUIET.
                }
                split; first by done.
                split; first by move: PREFIX => [_ [QUIET1 _]].
                move => t /andP [GT1 LT2] BUG.
                feed (MIN t).
                {
                  apply/andP; split;
                    first by apply/andP; split;
                      last by apply leq_trans with (n := t2); [by apply ltnW |].
                  apply/allP; intros j_hp ARR; apply/implyP; intro HP.
                  by apply BUG; last by apply actual_arrivals_arrived. 
                }
                by apply leq_ltn_trans with (p := t2) in MIN; first by rewrite ltnn in MIN.
              }
              {
                apply negbT in EX; rewrite negb_exists in EX; move: EX => /forallP ALL'.
                have ALL: forall t, t1 < t <= t1 + delta -> ~ quiet_time t.
                {
                  move => t /andP [GTt LEt] QUIET.
                  rewrite -ltnS in LEt.
                  specialize (ALL' (Ordinal LEt)); rewrite negb_and /= GTt orFb in ALL'. 
                  move: ALL' => /negP ALL'; apply ALL'; clear ALL'.
                  apply/allP; intros j_hp ARR; apply/implyP; intro HP.
                  by apply QUIET; last by apply actual_arrivals_arrived.
                } exfalso; clear ALL'.
                specialize (TOOMUCH ALL).
                by have BUG := leq_trans TOOMUCH BOUNDED; rewrite ltnn in BUG.
              }
            Qed.

          End UpperBound.

        End BoundingBusyInterval.

        (* In this section, we show that from a workload bound we can infer
           the existence of a busy interval. *)
        Section BusyIntervalFromWorkloadBound.

          (* Assume that for some delta > 0, the requested workload at
             time (t1 + delta) is bounded by delta (i.e., the supply). *)
          Variable delta: time.
          Hypothesis H_delta_positive: delta > 0.
          Hypothesis H_workload_is_bounded:
            forall t, actual_hp_workload t (t + delta) <= delta.

          (* Next, we assume that job j has positive cost, from which we can
             infer that there always is a time in which j is pending. *)
          Hypothesis H_positive_cost: job_cost j > 0.
          
          (* Therefore there must exists a busy interval [t1, t2) that
             contains the actual arrival time of job j. *)
          Corollary exists_busy_interval:
            exists t1 t2,
              t1 <= actual_job_arrival j < t2 /\
              t2 <= t1 + delta /\
              busy_interval t1 t2.
          Proof.
            have PREFIX := exists_busy_interval_prefix.
            rename H_workload_is_bounded into WORK.
            feed (PREFIX (actual_job_arrival j)).
            {
              apply/andP; split; first by apply leqnn.
              rewrite /completed_by /service /service_during.
              rewrite (cumulative_service_before_jitter_is_zero job_jitter) //.
              by rewrite eq_sym -lt0n H_positive_cost.
            }
            move: PREFIX => [t1 [PREFIX /andP [GE1 GEarr]]].
            have BOUNDED := busy_interval_is_bounded (actual_job_arrival j) t1 PREFIX delta.
            feed_n 2 BOUNDED; [by done | by apply WORK | ].
            move: BOUNDED => [t2 [GE2 BUSY]].
            exists t1, t2; split.
            {
              apply/andP; split; first by done.
              apply contraT; rewrite -leqNgt; intro BUG.
              move: BUSY PREFIX => [[LE12 _] QUIET] [_ [_ NOTQUIET]].
              feed (NOTQUIET t2); first by apply/andP; split.
              by exfalso; apply NOTQUIET.
            }
            by split.
          Qed.

          End BusyIntervalFromWorkloadBound.

        (* If we know that the workload is bounded, we can also use the
           busy interval to infer a response-time bound. *)
        Section ResponseTimeBoundFromBusyInterval.

          (* Assume that for some delta > 0, the requested workload
             at time (t1 + delta) is bounded by delta (i.e., the supply). *)
          Variable delta: time.
          Hypothesis H_delta_positive: delta > 0.
          Hypothesis H_workload_is_bounded:
            forall t,
              actual_hp_workload t (t + delta) <= delta.

          (* Then, job j must complete by (actual_job_arrival j + delta). *)
          Lemma busy_interval_bounds_response_time:
            job_completed_by j (actual_job_arrival j + delta).
          Proof.
            have BUSY := exists_busy_interval delta.
            destruct (job_cost j == 0) eqn:COST.
            {
              move: COST => /eqP COST.
              rewrite /job_completed_by /completed_by eqn_leq.
              apply/andP; split;
                first by apply cumulative_service_le_job_cost.
              by rewrite COST.
            }
            apply negbT in COST; rewrite -lt0n in COST.
            feed_n 3 BUSY; try (by done).
            move: BUSY => [t1 [t2 [/andP [GE1 LT2] [GE2 BUSY]]]].
            apply completion_monotonic with (t := t2); try (by done);
              first by apply leq_trans with (n := t1 + delta); [| by rewrite leq_add2r].
            apply job_completes_within_busy_interval with (t1 := t1) (t := actual_job_arrival j);
              try (by done); first by apply/andP; split.
            apply/andP; split; first by apply leqnn.
            rewrite /completed_by /service /service_during.
            rewrite (cumulative_service_before_jitter_is_zero job_jitter) //.
            by rewrite eq_sym -lt0n.
          Qed.

        End ResponseTimeBoundFromBusyInterval.
       
      End BoundingBusyInterval.
     
    End Lemmas.
    
  End Defs.

End BusyInterval.