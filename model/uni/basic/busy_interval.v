Require Import rt.util.all.
Require Import rt.model.task rt.model.job rt.model.arrival_sequence
               rt.model.priority rt.model.task_arrival.
Require Import rt.model.uni.schedule rt.model.uni.service
               rt.model.uni.workload.
Require Import rt.model.uni.basic.platform.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Module BusyInterval.

  Import Job UniprocessorSchedule Priority Platform
         Service Workload TaskArrival.

  (* In this section, we define the notion of a busy interval. *)
  Section Defs.

    Context {Task: eqType}.   
    Context {Job: eqType}.
    Variable job_cost: Job -> time.
    Variable job_task: Job -> Task.

    (* Assume any FP policy... *)
    Variable higher_eq_priority: FP_policy Task.
    
    (* ...and consider any uniprocessor schedule. *)
    Context {arr_seq: arrival_sequence Job}.
    Variable sched: schedule arr_seq.

    (* Let tsk be the task to be analyzed. *)
    Variable tsk: Task.
    
    (* For simplicity, let's define some local names. *)
    Let job_pending_at := pending job_cost sched.
    Let job_scheduled_at := scheduled_at sched.
    Let job_completed_by := completed_by job_cost sched.
    Let higher_or_equal_priority_job j_other :=
      higher_eq_priority (job_task j_other) tsk.

    (* We say that t is a quiet time for tsk iff every higher-priority
       job that arrived before t has completed by that time. *)
    Definition quiet_time (t: time) :=
      forall (j_hp: JobIn arr_seq),
        higher_or_equal_priority_job j_hp ->
        arrived_before j_hp t ->
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

      (* Recall the list of jobs that arrive in any interval. *)
      Let arrivals_between := jobs_arrived_between arr_seq.

      (* We begin by proving basic lemmas about the arrival and
         completion of jobs that are pending during a busy interval. *)
      Section BasicLemmas.

        (* Assume that the priority relation is reflexive. *)
        Hypothesis H_priority_is_reflexive:
          FP_is_reflexive higher_eq_priority.

        (* Consider any busy interval [t1, t2). *)
        Variable t1 t2: time.
        Hypothesis H_busy_interval: busy_interval t1 t2.

        (* Let j be any job of tsk... *)
        Variable j: JobIn arr_seq.
        Hypothesis H_job_of_tsk: job_task j = tsk.

        (* ...that is pending during the busy interval. *)
        Variable t: time.
        Hypothesis H_during_interval: t1 <= t < t2.
        Hypothesis H_job_is_pending: job_pending_at j t.

        (* First, we prove that job j completes by the end of the busy interval. *)
        Section CompletesDuringBusyInterval.
         
          Lemma job_completes_within_busy_interval:
            job_completed_by j t2.
          Proof.
            rename H_priority_is_reflexive into REFL,
                   H_busy_interval into BUSY, H_job_of_tsk into JOBtsk,
                   H_during_interval into INT, H_job_is_pending into PEND.
            move: BUSY => [_ QUIET].
            move: INT => /andP [_ LT2].
            apply QUIET;
              first by rewrite /higher_or_equal_priority_job -JOBtsk REFL.
            apply leq_ltn_trans with (n := t); last by done.
            by move: PEND => /andP [ARR _].
          Qed.         

        End CompletesDuringBusyInterval.

        (* Next, we prove that job j cannot have arrived before the
           busy interval. *)
        Section ArrivesDuringBusyInterval.

          (* Assume that jobs do not execute after completion. *)
          Hypothesis H_completed_jobs_dont_execute:
            completed_jobs_dont_execute job_cost sched.

          (* Then, we prove that j arrives no earlier than t1. *)
          Lemma job_arrives_within_busy_interval:
            t1 <= job_arrival j.
          Proof.
            rename H_priority_is_reflexive into REFL,
                   H_busy_interval into BUSY, H_job_of_tsk into JOBtsk,
                   H_during_interval into INT, H_job_is_pending into PEND.
            apply contraT; rewrite -ltnNge; intro LT1.
            move: BUSY => [[_ [QUIET _]] _].
            move: PEND => /andP [_ /negP NOTCOMP].
            move: INT => /andP [LE _].
            exfalso; apply NOTCOMP.
            apply completion_monotonic with (t0 := t1); try (by done).
            by apply QUIET;
              first by rewrite /higher_or_equal_priority_job JOBtsk REFL.
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
          exists (j: JobIn arr_seq),
            arrived_between j t1 t2 /\
            higher_eq_priority (job_task j) tsk /\
            ~ job_completed_by j t2. 
        Proof.
          rename H_quiet into QUIET, H_not_quiet into NOTQUIET.
          set hep := higher_eq_priority.
          destruct (has (fun j => (~~ job_completed_by j t2) && hep (job_task j) tsk)
                        (arrivals_between t1 t2)) eqn:COMP.
          {
            move: COMP => /hasP [j ARR /andP [NOTCOMP HP]].
            exists j; repeat split; [ | by done | by apply/negP].
            rewrite mem_filter in ARR; move: ARR => /andP [GE ARR].
            by apply/andP; split; last by apply JobIn_arrived.
          }
          {
            apply negbT in COMP; rewrite -all_predC in COMP.
            move: COMP => /allP COMP.
            exfalso; apply NOTQUIET; intros j HP ARR.
            destruct (ltnP (job_arrival j) t1) as [BEFORE | AFTER];
              first by specialize (QUIET j HP BEFORE); apply completion_monotonic with (t := t1).
            feed (COMP j);
              first by rewrite mem_filter; apply/andP; split; last by apply JobIn_arrived.
            unfold higher_or_equal_priority_job in *.
            by rewrite /= /hep HP andbT negbK in COMP.
          }
        Qed.

      End ExistsPendingJob.

      (* In this section, we prove that during a busy interval the
         processor is never idle. *)
      Section ProcessorAlwaysBusy.

        (* Assume that the schedule is work-conserving and that jobs do
           not execute before their arrival or after completion. *)
        Hypothesis H_work_conserving: work_conserving job_cost sched.
        Hypothesis H_completed_jobs_dont_execute: completed_jobs_dont_execute job_cost sched.
        Hypothesis H_jobs_must_arrive_to_execute: jobs_must_arrive_to_execute sched.
        
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
            feed (WORK j_hp t1);
              first by rewrite /arrived_before ltnS in ARR; repeat (apply/andP; split).
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

          (* If the schedule enforces an FP policy that is transitive, ...*)
          Hypothesis H_fixed_priority:
            enforces_FP_policy job_cost job_task sched higher_eq_priority.
          Hypothesis H_priority_is_transitive:
            FP_is_transitive higher_eq_priority.

          (* ... then the processor is always busy with a job of higher
             or equal priority (with respect to tsk). *)
          Lemma not_quiet_implies_exists_scheduled_hp_job:
            forall t,
              t1 <= t < t2 ->
              exists j_hp,
                arrived_between j_hp t1 t2 /\ 
                higher_eq_priority (job_task j_hp) tsk /\
                job_scheduled_at j_hp t.
          Proof.
            have NOTIDLE := not_quiet_implies_not_idle.
            unfold is_idle, FP_is_transitive, transitive in *.
            rename H_not_quiet into NOTQUIET, H_quiet into QUIET, H_priority_is_transitive into TRANS,
                   H_work_conserving into WORK, H_fixed_priority into FP.
            move => t /andP [GEt LEt].
            feed (NOTIDLE t); first by apply/andP; split; last by apply ltnW.
            destruct (sched t) eqn:SCHED; [clear NOTIDLE | by exfalso; apply NOTIDLE].
            move: SCHED => /eqP SCHED.
            exists j.
            have HP: higher_eq_priority (job_task j) tsk.
            {
              apply contraT; move => /negP NOTHP; exfalso.
              feed (NOTQUIET t.+1); first by apply/andP; split.
              apply NOTQUIET.
              unfold quiet_time, higher_or_equal_priority_job in *; intros j_hp HP ARR.
              apply contraT; move => /negP NOTCOMP'; exfalso.
              have BACK: backlogged job_cost sched j_hp t.
              {
                apply/andP; split; last first.
                {
                  apply/negP; intro SCHED'.
                  apply only_one_job_scheduled with (j1 := j) in SCHED'; last by done.
                  by subst j_hp; rewrite HP in NOTHP.
                }
                apply/andP; split; first by done.
                apply/negP; intro COMP; apply NOTCOMP'.
                by apply completion_monotonic with (t0 := t).
              }
              feed (FP j_hp j t BACK); first by done.
              by apply NOTHP, TRANS with (y := (job_task j_hp)).
            }
            repeat split; [| by done | by done].
            {
              move: (SCHED) => PENDING.
              apply scheduled_implies_pending with (job_cost0 := job_cost) in PENDING; try (by done).
              apply/andP; split;
                last by apply leq_ltn_trans with (n := t); first by move: PENDING => /andP [ARR _].
              apply contraT; rewrite -ltnNge; intro LT; exfalso.
              feed (QUIET j); first by done.
              specialize (QUIET LT).
              have COMP: job_completed_by j t by apply completion_monotonic with (t0 := t1).
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
        Hypothesis H_jobs_must_arrive_to_execute: jobs_must_arrive_to_execute sched.

        (* Also assume a work-conserving FP schedule, ... *)
        Hypothesis H_work_conserving: work_conserving job_cost sched.
        Hypothesis H_enforces_fp_policy:
          enforces_FP_policy job_cost job_task sched higher_eq_priority.

        (* ...in which the priority relation is reflexive and transitive. *)
        Hypothesis H_priority_is_reflexive: FP_is_reflexive higher_eq_priority.
        Hypothesis H_priority_is_transitive: FP_is_transitive higher_eq_priority.
        
        (* Let's recall the notions of service and workload of tasks with higher or equal
           priority (with respect to tsk). *)
        Let hp_service :=
          service_of_higher_or_equal_priority sched job_task higher_eq_priority tsk.
        Let hp_workload :=
          workload_of_higher_or_equal_priority job_cost job_task arr_seq higher_eq_priority tsk.

        (* Now we begin the proof. Let j be any job of tsk. *)
        Variable j: JobIn arr_seq.
        Hypothesis H_job_of_tsk: job_task j = tsk.

        (* In this section, we show that the busy interval is bounded. *)
        Section BoundingBusyInterval.

          (* Suppose that job j is pending at time t_busy. *)
          Variable t_busy: time.
          Hypothesis H_j_is_pending: job_pending_at j t_busy.
          
          (* First, we show that there must exist a busy interval prefix. *)
          Section LowerBound.
            
            (* Since job j is pending, there exists a (potentially unbounded)
               busy interval that starts prior to the arrival of j. *)
            Lemma exists_busy_interval_prefix:
              exists t1,
                busy_interval_prefix t1 t_busy.+1 /\
                t1 <= job_arrival j <= t_busy.
            Proof.
              rename H_j_is_pending into PEND, H_job_of_tsk into JOBtsk,
                     H_work_conserving into WORK, H_priority_is_reflexive into REFL,
                     H_enforces_fp_policy into FP.
              unfold busy_interval_prefix.
              set dec_quiet :=
                fun t => all
                           (fun (j: JobIn arr_seq) =>
                              higher_eq_priority (job_task j) tsk ==> (completed_by job_cost sched j t))
                           (jobs_arrived_before arr_seq t).
              destruct ([exists t:'I_t_busy.+1, dec_quiet t]) eqn:EX.
              {
                set last := \max_(t < t_busy.+1 | dec_quiet t) t.
                move: EX => /existsP [t EX].
                have PRED: dec_quiet last by apply (bigmax_pred t_busy.+1 dec_quiet t).
                have QUIET: quiet_time last.
                {
                  move: PRED => /allP PRED.
                  intros j_hp HP ARR; apply JobIn_arrived in ARR.
                  specialize (PRED j_hp ARR).
                  by move: PRED => /implyP PRED; apply PRED.
                }
                exists last.
                split; last first.
                {
                  apply/andP; split; last by move: PEND => /andP [ARR _].
                  apply contraT; rewrite -ltnNge; intros BEFORE.
                  unfold quiet_time, higher_or_equal_priority_job in *.
                  feed (QUIET j); first by rewrite JOBtsk REFL.
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
                    apply JobIn_arrived in ARR.
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
                split; first by intros j_hp _ ARR; rewrite /arrived_before ltn0 in ARR.
                move => t /andP [GE LT].
                specialize (ALL (Ordinal LT)); move: ALL => /negP ALL.
                intros QUIET; apply ALL; simpl.
                apply/allP; intros j_hp ARR; apply/implyP; intros HP.
                apply JobIn_arrived in ARR.
                by apply QUIET.
              }
            Qed.

          End LowerBound.
        
        (* Next we prove that, if there is a point where the requested workload
           is upper-bounded by the supply, then the busy interval eventually ends. *)
          Section UpperBound.

            (* Consider any busy interval that starts at time t1 <= job_arrival j. *)
            Variable t1: time.
            Hypothesis H_is_busy_prefix: busy_interval_prefix t1 t_busy.+1.
            Hypothesis H_busy_prefix_contains_arrival: job_arrival j >= t1.

            (* Next, assume that for some delta > 0, the requested workload
               at time (t1 + delta) is bounded by delta (i.e., the supply). *)
            Variable delta: time.
            Hypothesis H_delta_positive: delta > 0.
            Hypothesis H_workload_is_bounded: hp_workload t1 (t1 + delta) <= delta.

            (* If there exists a quiet time by time (t1 + delta), it trivially follows that
               the busy interval is bounded.
               Thus, let's consider first the harder case where there is no quiet time,
               which turns out to be impossible. *)
            Section CannotBeBusyForSoLong.

              (* Assume that there is no quiet time in the interval (t1, t1 + delta]. *)
              Hypothesis H_no_quiet_time:
                forall t, t1 < t <= t1 + delta -> ~ quiet_time t.

              (* Since the interval is always non-quiet, the processor is always busy
                 with tasks of higher-or-equal priority. *)
              Lemma busy_interval_has_uninterrupted_service:
                hp_service t1 (t1 + delta) = delta.
              Proof.
                rename H_is_busy_prefix into PREFIX.
                have EXISTS := not_quiet_implies_exists_scheduled_hp_job.
                feed_n 3 EXISTS; try (by done).
                apply eq_trans with (y := \sum_(t1 <= t < t1 + delta) 1);
                  last by simpl_sum_const; rewrite addKn.
                unfold hp_service, service_of_higher_or_equal_priority, service_of_jobs.
                rewrite exchange_big /=.
                apply eq_big_nat; move => t /andP [GEt LTt].
                move: PREFIX => [_ [QUIET _]].
                have EX: exists j_hp : JobIn arr_seq,
                           arrived_between j_hp t1 (t1 + delta) /\
                           higher_eq_priority (job_task j_hp) tsk /\
                           scheduled_at sched j_hp t.
                {
                  apply EXISTS with (t1 := t1) (t2 := t1 + delta); try (by done);
                    last by apply/andP; split.
                  by rewrite -addn1; apply leq_add.
                } clear EXISTS.
                move: EX => [j_hp [/andP [GE LT] [HP SCHED]]].
                rewrite big_mkcond (bigD1_seq j_hp) /=; first last.
                - by rewrite filter_uniq //; apply JobIn_uniq.
                - by rewrite mem_filter; apply/andP; split; last by apply JobIn_arrived.
                rewrite HP big1; first by rewrite /service_at SCHED addn0.
                intros j' NEQ; destruct (higher_eq_priority (job_task j') tsk); last by done.
                apply/eqP; rewrite eqb0; apply/negP; move => SCHED'.
                move: NEQ => /eqP NEQ; apply NEQ.
                by apply only_one_job_scheduled with (sched0 := sched) (t0 := t).
              Qed.

              (* Moreover, the fact that the interval is not quiet also implies
                 that there's more workload requested than service received. *)
              Lemma busy_interval_too_much_workload:
                hp_workload t1 (t1 + delta) > hp_service t1 (t1 + delta).
              Proof.
                have PEND := not_quiet_implies_exists_pending_job 
                             H_completed_jobs_dont_execute.
                rename H_no_quiet_time into NOTQUIET, 
                       H_is_busy_prefix into PREFIX, H_enforces_fp_policy into FP.
                set l := jobs_arrived_between arr_seq t1 (t1 + delta).
                set hep := higher_eq_priority.
                unfold hp_service, service_of_higher_or_equal_priority, service_of_jobs,
                       hp_workload, workload_of_higher_or_equal_priority, workload_of_jobs.
                fold arrivals_between l hep.
                move: (PREFIX) => [_ [QUIET _]].
                move: (NOTQUIET) => NOTQUIET'.
                feed (NOTQUIET' (t1 + delta));
                  first by apply/andP; split;
                    first by rewrite -addn1; apply leq_add.
                feed (PEND t1 (t1 + delta)); first by apply leq_addr.
                specialize (PEND QUIET NOTQUIET').
                move: PEND => [j0 [/andP [GE0 LT0] [HP0 NOTCOMP0]]].
                have IN0: j0 \in l.
                  by rewrite mem_filter; apply/andP; split; last by apply JobIn_arrived.
                have UNIQ: uniq l by rewrite filter_uniq //; apply JobIn_uniq.
                rewrite big_mkcond [\sum_(_ <- _ | hep _ _)_]big_mkcond.
                rewrite (bigD1_seq j0); [simpl | by done | by done].
                rewrite (bigD1_seq j0); [simpl | by done | by done].
                rewrite /hep HP0.
                rewrite -add1n addnA [1 + _]addnC addn1.
                apply leq_add; last first.
                {
                  apply leq_sum; intros j1 NEQ.
                  destruct (higher_eq_priority (job_task j1) tsk); last by done.
                  by apply cumulative_service_le_job_cost. 
                }
                rewrite ltn_neqAle; apply/andP; split; last by apply cumulative_service_le_job_cost.
                unfold service_during.
                rewrite ignore_service_before_arrival; rewrite //; [| by apply ltnW].
                rewrite <- ignore_service_before_arrival with (t2:=0); rewrite //; [|by apply ltnW].
                by apply/negP.
              Qed.

              (* Using the two lemmas above, we infer that the workload is larger than the
                 interval length. However, this contradicts the assumption H_workload_is_bounded. *)
              Corollary busy_interval_workload_larger_than_interval:
                hp_workload t1 (t1 + delta) > delta.
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
                           (fun (j: JobIn arr_seq) =>
                              higher_eq_priority (job_task j) tsk ==> (completed_by job_cost sched j t))
                           (jobs_arrived_before arr_seq t).

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
                  feed (QUIET j_hp); first by rewrite JobIn_arrived.
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
                  by apply BUG; last by rewrite -JobIn_arrived.
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
                  by apply QUIET; last by rewrite -JobIn_arrived.
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
            forall t, hp_workload t (t + delta) <= delta.

          (* By assuming that job j has positive cost, we can infer that
             there always is a time in which j is pending. *)
          Hypothesis H_positive_cost: job_cost j > 0.
          
          (* Therefore there must exists a busy interval [t1, t2) that
             contains the arrival time of j. *)
          Corollary exists_busy_interval:
            exists t1 t2,
              t1 <= job_arrival j < t2 /\
              t2 <= t1 + delta /\
              busy_interval t1 t2.
          Proof.
            have PREFIX := exists_busy_interval_prefix.
            rename H_workload_is_bounded into WORK.
            feed (PREFIX (job_arrival j)).
            {
              apply/andP; split; first by apply leqnn.
              rewrite /completed_by /service /service_during.
              rewrite ignore_service_before_arrival //.
              rewrite big_geq; last by apply leqnn.
              by rewrite eq_sym -lt0n H_positive_cost.
            }
            move: PREFIX => [t1 [PREFIX /andP [GE1 GEarr]]].
            have BOUNDED := busy_interval_is_bounded (job_arrival j) t1 PREFIX delta.
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
              hp_workload t (t + delta) <= delta.

          (* Then, job j must complete by (job_arrival j + delta). *)
          Lemma busy_interval_bounds_response_time:
            job_completed_by j (job_arrival j + delta).
          Proof.
            have BUSY := exists_busy_interval delta.
            rename H_job_of_tsk into JOBtsk.
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
            apply job_completes_within_busy_interval with (t1 := t1) (t := job_arrival j);
              try (by done); first by apply/andP; split.
            apply/andP; split; first by apply leqnn.
            rewrite /completed_by /service /service_during.
            rewrite ignore_service_before_arrival //.
            rewrite big_geq; last by apply leqnn.
            by rewrite eq_sym -lt0n.
          Qed.

        End ResponseTimeBoundFromBusyInterval.
       
      End BoundingBusyInterval.
     
    End Lemmas.
    
  End Defs.

End BusyInterval.