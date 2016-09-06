Require Import rt.util.all.
Require Import rt.model.job rt.model.arrival_sequence rt.model.suspension.
Require Import rt.model.uni.schedule.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Module SuspensionIntervals.

  Export Job UniprocessorSchedule Suspension.

  (* In this section we define job suspension intervals in a schedule. *)
  Section DefiningSuspensionIntervals.

    Context {Job: eqType}.
    Variable job_cost: Job -> time.

    (* Consider any job suspension times... *)
    Variable next_suspension: job_suspension Job.

    (* ...and any uniprocessor schedule. *)
    Context {arr_seq: arrival_sequence Job}.
    Variable sched: schedule arr_seq.

    (* For simplicity, let's define some local names. *)
    Let job_scheduled_at := scheduled_at sched.
    Let job_completed_by := completed_by job_cost sched.

    (* In this section, we define when jobs may begin to suspend. *)
    Section BeginningOfSuspension.

      Section Defs.
        
        (* Let j be any job in the arrival sequence. *)
        Variable j: JobIn arr_seq.

        (* Next, we will show how to find the most recent self-suspension
           incurred by job j in the interval [0, t], if exists.
           As we will show next, that corresponds to the time after the most
           recent execution of job in the interval [0, t). *)
        Variable t: time.
        
        (* Let scheduled_before denote whether job j was scheduled in the interval [0, t). *)
        Let scheduled_before :=
          [exists t0: 'I_t, job_scheduled_at j t0].

        (* In case j was scheduled before, we define the last time in which j was scheduled. *)
        Let last_time_scheduled :=
          \max_(t_last < t | job_scheduled_at j t_last) t_last.

        (* Then, the most recent self-suspension of job j in the interval [0, t], if exists,
           occurs:
             (a) immediately after the last time in which job j was scheduled, or,
             (b) if j was never scheduled, at the arrival time of j. *)
        Definition time_after_last_execution :=
          if scheduled_before then
            last_time_scheduled + 1
          else job_arrival j.

      End Defs.

      (* Next, we prove lemmas about the time following the last execution. *)
      Section Lemmas.

        (* Let j be any job in the arrival sequence. *)
        Variable j: JobIn arr_seq.

        (* In this section, we show that the time after the last execution occurs
           no earlier than the arrival of the job. *)
        Section JobHasArrived.

          (* Assume that jobs do not execute before they arrived. *)
          Hypothesis H_jobs_must_arrive_to_execute:
            jobs_must_arrive_to_execute sched.
          
          (* Then, the time following the last execution of job j in the
             interval [0, t) occurs no earlier than the arrival of j. *)
          Lemma last_execution_after_arrival:
            forall t,
              has_arrived j (time_after_last_execution j t).
          Proof.
            unfold time_after_last_execution, has_arrived; intros t.
            case EX: [exists _, _]; last by done.
            move: EX => /existsP [t0 SCHED].
            apply leq_trans with (n := t0 + 1);
              last by rewrite leq_add2r; apply leq_bigmax_cond.
            apply leq_trans with (n := t0); last by rewrite addn1.
            by apply H_jobs_must_arrive_to_execute.
          Qed.

        End JobHasArrived.

        (* Next, we establish the monotonicity of the function. *)
        Section Monotonicity.

          (* Assume that jobs do not execute before they arrived. *)
          Hypothesis H_jobs_must_arrive_to_execute:
            jobs_must_arrive_to_execute sched.

          (* Let t1 be any time no earlier than the arrival of job j. *)
          Variable t1: time.
          Hypothesis H_after_arrival: has_arrived j t1.

          (* Then, (time_after_last_execution j) grows monotonically
             after that point. *)
          Lemma last_execution_monotonic:
            forall t2,
              t1 <= t2 ->
              time_after_last_execution j t1 <= time_after_last_execution j t2.
          Proof.
            rename H_jobs_must_arrive_to_execute into ARR.
            intros t2 LE12.
            rewrite /time_after_last_execution.
            case EX1: [exists _, _].
            {
              move: EX1 => /existsP [t0 SCHED0].
              have EX2: [exists t:'I_t2, job_scheduled_at j t].
              {
                have LT: t0 < t2 by apply: (leq_trans _ LE12).
                by apply/existsP; exists (Ordinal LT).
              }
              rewrite EX2 2!addn1.
              set m1 := \max_(_ < t1 | _)_.
              have LTm1: m1 < t2.
              {
                apply: (leq_trans _ LE12).
                by apply bigmax_ltn_ord with (i0 := t0).
              }
              apply leq_ltn_trans with (n := Ordinal LTm1); first by done.
              by apply leq_bigmax_cond, (bigmax_pred _ _ t0).
            }
            {
              case EX2: [exists _, _]; last by done.
              move: EX2 => /existsP [t0 SCHED0].
              set m2 := \max_(_ < t2 | _)_.
              rewrite addn1 ltnW // ltnS.
              have SCHED2: scheduled_at sched j m2 by apply (bigmax_pred _ _ t0).
              by apply ARR in SCHED2.
            }
          Qed.

        End Monotonicity.

        (* Next, we prove that the function is idempotent. *)
        Section Idempotence.

          (* Assume that jobs do not execute before they arrived. *)
          Hypothesis H_jobs_must_arrive_to_execute:
            jobs_must_arrive_to_execute sched.
          
          (* Then, we prove that the time following the last execution of
             job j is an idempotent function. *)
          Lemma last_execution_idempotent:
            forall t,
              time_after_last_execution j (time_after_last_execution j t)
              = time_after_last_execution j t.
          Proof.
            rename H_jobs_must_arrive_to_execute into ARR.
            intros t.
            rewrite {2 3}/time_after_last_execution.
            case EX: [exists _,_].
            {
              move: EX => /existsP [t0 SCHED].
              rewrite /time_after_last_execution.
              set ex := [exists t0, _].
              have EX': ex.
              {
                apply/existsP; rewrite addn1.
                exists (Ordinal (ltnSn _)).
                by apply bigmax_pred with (i0 := t0).
              }
              rewrite EX'; f_equal.
              rewrite addn1; apply/eqP.
              set m := \max_(_ < t | _)_.
              have LT: m < m.+1 by done.
              rewrite eqn_leq; apply/andP; split.
              {
                rewrite -ltnS; apply bigmax_ltn_ord with (i0 := Ordinal LT).
                by apply bigmax_pred with (i0 := t0).
              }
              {
                apply leq_trans with (n := Ordinal LT); first by done.
                by apply leq_bigmax_cond, bigmax_pred with (i0 := t0).
              }
            }
            {
              apply negbT in EX; rewrite negb_exists in EX.
              move: EX => /forallP EX.
              rewrite /time_after_last_execution.
              set ex := [exists _, _].
              suff EX': ex = false; first by rewrite EX'.
              apply negbTE; rewrite negb_exists; apply/forallP.
              intros x.
              apply/negP; intro SCHED.
              apply ARR in SCHED.
              by apply leq_ltn_trans with (p := job_arrival j) in SCHED;
                first by rewrite ltnn in SCHED.
            }
          Qed.

        End Idempotence.

        (* Next, we show that time_after_last_execution is bounded by the identity function. *)
        Section BoundedByIdentity.
          
          (* Let t be any time no earlier than the arrival of j. *)
          Variable t: time.
          Hypothesis H_after_arrival: has_arrived j t.

          (* Then, the time following the last execution of job j in the interval [0, t)
             occurs no later than time t. *)
          Lemma last_execution_bounded_by_identity:
              time_after_last_execution j t <= t.
          Proof.
            unfold time_after_last_execution.
            case EX: [exists _, _]; last by done.
            move: EX => /existsP [t0 SCHED].
            by rewrite addn1; apply bigmax_ltn_ord with (i0 := t0).
          Qed.

        End BoundedByIdentity.

        (* In this section, we show that if the service received by a job
           remains the same, the time after last execution also doesn't change. *)
        Section SameLastExecution.
          
          (* Consider any time instants t and t'... *)
          Variable t t': time.

          (* ...in which job j has received the same amount of service. *)
          Hypothesis H_same_service: service sched j t = service sched j t'.

          (* Then, we prove that the times after last execution relative to
             instants t and t' are exactly the same. *)
          Lemma same_service_implies_same_last_execution:
            time_after_last_execution j t = time_after_last_execution j t'.
          Proof.
            rename H_same_service into SERV.
            have IFF := same_service_implies_scheduled_at_earlier_times
                          sched j t t' SERV.
            rewrite /time_after_last_execution.
            rewrite IFF; case EX2: [exists _, _]; [f_equal | by done].
            have EX1: [exists x: 'I_t, job_scheduled_at j x] by rewrite IFF.
            clear IFF.
            move: t t' SERV EX1 EX2 => t1 t2; clear t t'.
            wlog: t1 t2 / t1 <= t2 => [EQ SERV EX1 EX2 | LE].
              by case/orP: (leq_total t1 t2); ins; [|symmetry]; apply EQ.
            
            set m1 := \max_(t < t1 | job_scheduled_at j t) t.
            set m2 := \max_(t < t2 | job_scheduled_at j t) t.
            move => SERV /existsP [t1' SCHED1'] /existsP [t2' SCHED2'].
            apply/eqP; rewrite eqn_leq; apply/andP; split.
            {
              have WID := big_ord_widen_cond t2
                           (fun x => job_scheduled_at j x) (fun x => x).
              rewrite /m1 /m2 {}WID //.
              rewrite big_mkcond [\max_(t < t2 | _) _]big_mkcond.
              apply leq_big_max; intros i _.
              case AND: (_ && _); last by done.
              by move: AND => /andP [SCHED _]; rewrite SCHED.
            }
            {
              destruct (leqP t2 m1) as [GEm1 | LTm1].
              {
                apply leq_trans with (n := t2); last by done.
                by apply ltnW, bigmax_ltn_ord with (i0 := t2').
              }
              destruct (ltnP m2 t1) as [LTm2 | GEm2].
              {
                apply leq_trans with (n := Ordinal LTm2); first by done.
                by apply leq_bigmax_cond, bigmax_pred with (i0 := t2').
              }
              have LTm2: m2 < t2 by apply bigmax_ltn_ord with (i0 := t2').
              have SCHEDm2: job_scheduled_at j m2 by apply bigmax_pred with (i0 := t2').
              exfalso; move: SERV => /eqP SERV.
              rewrite -[_ == _]negbK in SERV.
              move: SERV => /negP SERV; apply SERV; clear SERV.
              rewrite neq_ltn; apply/orP; left.
              rewrite /service /service_during.
              rewrite -> big_cat_nat with (n := m2) (p := t2);
                [simpl | by done | by apply ltnW].
              rewrite -addn1; apply leq_add; first by apply extend_sum. 
              destruct t2; first by rewrite ltn0 in LTm1.
              rewrite big_nat_recl; last by done.
              by rewrite /service_at -/job_scheduled_at SCHEDm2.
            }
          Qed.

        End SameLastExecution.

        (* In this section, we show that the service received by a job
         does not change since the last execution. *)
        Section SameService.

          (* Assume that jobs do not execute before they arrived. *)
          Hypothesis H_jobs_must_arrive_to_execute:
            jobs_must_arrive_to_execute sched.

          (* Then, we prove that, for any time t, the service received by job j
           before (time_after_last_execution j t) is the same as the service
           by j before time t. *)
          Lemma same_service_since_last_execution:
            forall t,
              service sched j (time_after_last_execution j t) = service sched j t.
          Proof.
            intros t; rewrite /time_after_last_execution.
            case EX: [exists _, _].
            {
              move: EX => /existsP [t0 SCHED0].
              set m := \max_(_ < _ | _) _; rewrite addn1.
              have LTt: m < t by apply: (bigmax_ltn_ord _ _ t0).
              rewrite leq_eqVlt in LTt.
              move: LTt => /orP [/eqP EQ | LTt]; first by rewrite EQ.
              rewrite {2}/service/service_during.
              rewrite -> big_cat_nat with (n := m.+1);
                [simpl | by done | by apply ltnW].
              rewrite [X in _ + X]big_nat_cond [X in _ + X]big1 ?addn0 //.
              move => i /andP [/andP [GTi LTi] _].
              apply/eqP; rewrite eqb0; apply/negP; intro BUG.
              have LEi: (Ordinal LTi) <= m by apply leq_bigmax_cond.
                by apply (leq_ltn_trans LEi) in GTi; rewrite ltnn in GTi.
            }
            {
              apply negbT in EX; rewrite negb_exists in EX.
              move: EX => /forallP ALL.
              rewrite /service /service_during.
              rewrite ignore_service_before_arrival // big_geq //.
              rewrite big_nat_cond big1 //; move => i /andP [/= LTi _].
                by apply/eqP; rewrite eqb0; apply (ALL (Ordinal LTi)).
            }
          Qed.

        End SameService.

        (* In this section, we show that for any smaller value of service, we can
         always find the last execution that corresponds to that service. *)
        Section ExistsIntermediateExecution.

          (* Assume that jobs do not execute before they arrived. *)
          Hypothesis H_jobs_must_arrive_to_execute:
            jobs_must_arrive_to_execute sched.
          
          (* Assume that job j has completed by time t. *)
          Variable t: time.
          Hypothesis H_j_has_completed: completed_by job_cost sched j t.

          (* Then, for any value of service less than the cost of j, ...*)
          Variable s: time.
          Hypothesis H_less_than_cost: s < job_cost j.

          (* ...there exists a last execution where the service received
           by job j equals s. *)
          Lemma exists_last_execution_with_smaller_service:
            exists t0,
              service sched j (time_after_last_execution j t0) = s.
          Proof.
            have SAME := same_service_since_last_execution.
            rename H_jobs_must_arrive_to_execute into ARR.
            move: H_j_has_completed => /eqP COMP.
            feed (exists_intermediate_point (service sched j));
              first by apply service_is_a_step_function.
            move => EX; feed (EX (job_arrival j) t).
            {
              feed (cumulative_service_implies_scheduled sched j 0 t);
                first by apply leq_ltn_trans with (n := s);
                last by rewrite -/(service _ _ _) COMP.
              move => [t' [/= LTt SCHED]].
              apply leq_trans with (n := t'); last by apply ltnW.
                by apply ARR in SCHED.
            }
            feed (EX s).
            {
              apply/andP; split; last by rewrite COMP.
              rewrite /service /service_during.
                by rewrite ignore_service_before_arrival // big_geq.
            }
            move: EX => [x_mid [_ SERV]]; exists x_mid.
              by rewrite -SERV SAME.
          Qed.

        End ExistsIntermediateExecution.
        
      End Lemmas.
      
    End BeginningOfSuspension.

    (* Having identified the time after last execution, we now define
       whether jobs are suspended. *)
    Section JobSuspension.
      
      (* Let j be any job in the arrival sequence. *)
      Variable j: JobIn arr_seq.

      Section DefiningSuspension.
        
        (* We are going to define whether job j is suspended at time t. *)
        Variable t: time.

        (* First, we define the (potential) begin of the latest self suspension as the
           time following the last execution of job j in the interval [0, t).
           (Note that suspension_start can return time t itself.) *)
        Let suspension_start := time_after_last_execution j t.

        (* Next, using the service received by j in the interval [0, suspension_start), ... *)
        Let current_service := service sched j suspension_start.

        (* ... we recall the duration of the suspension expected for job j after having
           received that amount of service. *)
        Definition suspension_duration := next_suspension j current_service.

        (* Then, we say that job j is suspended at time t iff j has not completed
           by time t and t lies in the latest suspension interval. *)
        Definition suspended_at :=
          ~~ completed_by job_cost sched j t &&
          (suspension_start <= t < suspension_start + suspension_duration).

      End DefiningSuspension.

      (* Based on the notion of suspension, we also define the cumulative
         suspension time of job j in any interval [t1, t2)... *)
      Definition cumulative_suspension_during (t1 t2: time) :=
        \sum_(t1 <= t < t2) (suspended_at t).

      (* ...and the cumulative suspension time in any interval [0, t). *)
      Definition cumulative_suspension (t: time) := cumulative_suspension_during 0 t.

    End JobSuspension.

    (* Next, we define whether the schedule respects self-suspensions. *)
    Section SuspensionAwareSchedule.

      (* We say that the schedule respects self-suspensions iff suspended
         jobs are never scheduled. *)
      Definition respects_self_suspensions :=
        forall j t,
          job_scheduled_at j t -> ~ suspended_at j t.

    End SuspensionAwareSchedule.
    
    (* In this section, we prove several results related to job suspensions. *)
    Section Lemmas.

      (* First, we prove that at any time within any suspension interval, 
         a job is always suspended. *)
      Section InsideSuspensionInterval.

        (* Assume that jobs do not execute before they arrive... *)
        Hypothesis H_jobs_must_arrive_to_execute:
          jobs_must_arrive_to_execute sched.

        (* ...and nor after completion. *)
        Hypothesis H_completed_jobs_dont_execute:
          completed_jobs_dont_execute job_cost sched.
      
        (* Assume that the schedule respects self-suspensions. *)
        Hypothesis H_respects_self_suspensions: respects_self_suspensions.
      
        (* Let j be any job in the arrival sequence. *)
        Variable j: JobIn arr_seq.

        (* Consider any time t after the arrival of j... *)
        Variable t: time.
        Hypothesis H_has_arrived: has_arrived j t.

        (* ...and recall the latest suspension interval of job j relative to time t. *)
        Let suspension_start := time_after_last_execution j t.
        Let duration := suspension_duration j t.

        (* First, we analyze the service received during a suspension interval. *)
        Section SameService.
          
          (* Let t_in be any time in the suspension interval relative to time t. *)
          Variable t_in: time.
          Hypothesis H_within_suspension_interval:
            suspension_start <= t_in <= suspension_start + duration.

          (* Then, we show that the service received before time t_in
             equals the service received before the beginning of the
             latest suspension interval (if exists). *)
          Lemma same_service_in_suspension_interval:
            service sched j t_in = service sched j suspension_start.
          Proof.
            rename H_within_suspension_interval into BETWEEN,
                   H_respects_self_suspensions into SUSP, t_in into i.
            generalize dependent i.
            suff SAME:
              forall delta,
                delta <= duration ->
                service sched j (suspension_start + delta) =
                service sched j suspension_start.
            {
              move => i /andP [GE LT].
              feed (SAME (i-suspension_start)); first by rewrite leq_subLR.
              by rewrite addnBA // addKn in SAME.
            }
            induction delta; first by rewrite addn0.
            intros LT.
            feed IHdelta; first by apply ltnW.
            rewrite addnS -[service _ _ suspension_start]addn0.
            rewrite /service /service_during big_nat_recr //=.
            f_equal; first by done.
            apply/eqP; rewrite eqb0; apply/negP; intro SCHED.
            move: (SCHED) => SCHED'.
            apply SUSP in SCHED; apply SCHED; clear SCHED.
            rewrite /suspended_at /suspension_duration.
            case: (boolP (completed_by _ _ _ _)) => [COMP | NOTCOMP];
              first by apply completed_implies_not_scheduled in COMP;
                first by rewrite SCHED' in COMP.
            rewrite andTb (same_service_implies_same_last_execution _ _ suspension_start) //.
            rewrite /suspension_start last_execution_idempotent //.
            apply/andP; split; first by apply leq_addr.
            by rewrite ltn_add2l.
          Qed.

        End SameService.

        (* Next, we infer that the job is suspended at all times during
           the suspension interval. *)
        Section JobSuspendedAtAllTimes.

          (* Let t_in be any time before the completion of job j. *)
          Variable t_in: time.
          Hypothesis H_not_completed: ~~ job_completed_by j t_in.

          (* If t_in lies in the suspension interval relative to time t, ...*)
          Hypothesis H_within_suspension_interval:
            suspension_start <= t_in < suspension_start + duration.

          (* ...then job j is suspended at time t_in. More precisely, the suspension
             interval relative to time t_in is included in the suspension interval
             relative to time t. *)
          Lemma suspended_in_suspension_interval:
            suspended_at j t_in.
          Proof.
            rename H_within_suspension_interval into BETWEEN.
            move: BETWEEN => /andP [GE LT].
            have ARR: has_arrived j t_in.
            {
              by apply leq_trans with (n := suspension_start);
                first by apply last_execution_after_arrival.
            }
            apply/andP; split; first by done.
            apply/andP; split;
              first by apply last_execution_bounded_by_identity.
            apply (leq_trans LT).
            have SAME: time_after_last_execution j t = time_after_last_execution j t_in.
            {
              set b := _ _ t.
              rewrite [_ _ t_in](same_service_implies_same_last_execution _ _ b);
                first by rewrite last_execution_idempotent.
              apply same_service_in_suspension_interval.
              by apply/andP; split; last by apply ltnW.
            }
            rewrite /suspension_start SAME leq_add2l.
            by rewrite /duration /suspension_duration SAME.
          Qed.
 
        End JobSuspendedAtAllTimes.
        
      End InsideSuspensionInterval.
      
      (* Next, we prove lemmas about the state of a suspended job. *)
      Section StateOfSuspendedJob.

        (* Assume that jobs do not execute before they arrived. *)
        Hypothesis H_jobs_must_arrive_to_execute:
          jobs_must_arrive_to_execute sched.
        
        (* Let j be any job in the arrival sequence. *)
        Variable j: JobIn arr_seq.

        (* Assume that j is suspended at time t. *)
        Variable t: time.
        Hypothesis H_j_is_suspended: suspended_at j t.

        (* First, we show that j must have arrived by time t. *)
        Lemma suspended_implies_arrived: has_arrived j t. 
        Proof.
          rename H_j_is_suspended into SUSP.
          move: SUSP => /andP [_ SUSP].
          rewrite -[_ && _]negbK in SUSP; move: SUSP => /negP SUSP.
          rewrite /has_arrived leqNgt; apply/negP; intro LT.
          apply SUSP; clear SUSP.
          rewrite negb_and; apply/orP; left.
          rewrite -ltnNge.
          apply: (leq_trans LT); clear LT.
          rewrite /time_after_last_execution.
          case EX: [exists _, _]; last by apply leqnn.
          set t' := \max_(_ < _ | _)_.
          move: EX => /existsP [t0 EX].
          apply bigmax_pred in EX; rewrite -/t' /job_scheduled_at in EX.
          apply leq_trans with (n := t'); last by apply leq_addr.
          rewrite leqNgt; apply/negP; intro LT.
          have NOTSCHED: ~~ scheduled_at sched j t'.
          {
            rewrite -eqb0; apply/eqP.
            by apply service_before_job_arrival_zero; first by done.
          }
          by rewrite EX in NOTSCHED.
        Qed.

        (* By the definition of suspension, it also follows that j cannot
           have completed by time t. *)
        Corollary suspended_implies_not_completed:
          ~~ completed_by job_cost sched j t.
        Proof.
          by move: H_j_is_suspended => /andP [NOTCOMP _].
        Qed.

      End StateOfSuspendedJob.

      (* Next, we establish a bound on the cumulative suspension time of any job. *)
      Section BoundOnCumulativeSuspension.

        (* Assume that jobs do not execute before they arrive... *)
        Hypothesis H_jobs_must_arrive_to_execute:
          jobs_must_arrive_to_execute sched.

        (* ...and nor after completion. *)
        Hypothesis H_completed_jobs_dont_execute:
          completed_jobs_dont_execute job_cost sched.
      
        (* Assume that the schedule respects self-suspensions. *)
        Hypothesis H_respects_self_suspensions: respects_self_suspensions.

        (* Let j be any job in the arrival sequence. *)
        Variable j: JobIn arr_seq.

        (* Recall the total suspension of job j as given by the dynamic suspension model. *)
        Let cumulative_suspension_of_j :=
          cumulative_suspension_during j.
        Let total_suspension_of_j :=
          total_suspension job_cost next_suspension j.

        (* We prove that the cumulative suspension time of job j in any
           interval is upper-bounded by the total suspension time. *)
        Lemma cumulative_suspension_le_total_suspension:
          forall t1 t2,
            cumulative_suspension_of_j t1 t2 <= total_suspension_of_j.
        Proof.
          unfold cumulative_suspension_of_j, cumulative_suspension_during,
                 total_suspension_of_j, total_suspension.
          intros t1 t2.
          apply leq_trans with (n := \sum_(0 <= s < job_cost j)
                                      \sum_(t1 <= t < t2 | service sched j t == s) suspended_at j t).
          {
            rewrite (exchange_big_dep_nat (fun x => true)) //=.
            apply leq_sum; intros s _.
            destruct (boolP (suspended_at j s)) as [SUSP | NOTSUSP]; last by done.
            rewrite (big_rem (service sched j s)); first by rewrite eq_refl.
            rewrite mem_index_iota; apply/andP; split; first by done.
            rewrite ltn_neqAle; apply/andP; split; last by apply cumulative_service_le_job_cost.
            by apply suspended_implies_not_completed in SUSP.
          }
          {
            apply leq_sum_nat; move => s /andP [_ LT] _.
            destruct (boolP [exists t: 'I_t2, (t >= t1) && (service sched j t == s)]) as [EX | ALL];
              last first.
            {
              rewrite negb_exists in ALL; move: ALL => /forallP ALL.
              rewrite big_nat_cond big1 //.
              move => i /andP [/andP [GEi LTi] SERV].
              by specialize (ALL (Ordinal LTi)); rewrite /= SERV GEi andbT in ALL.
            }
            move: EX => /existsP [t' /andP [GE' /eqP SERV]].
            unfold suspended_at, suspension_duration.
            set b := time_after_last_execution j.
            set n := next_suspension j s.
            apply leq_trans with (n := \sum_(t1 <= t < t2 | b t' <= t < b t' + n) 1).
            {
              rewrite big_mkcond [\sum_(_ <= _ < _ | b t' <= _ < _) _]big_mkcond /=.
              apply leq_sum_nat; intros t LEt _.
              case: (boolP (completed_by _ _ _ _)) => [COMP | NOTCOMP];
                [by case (_ == _) | simpl].
              case EQ: (service _ _ _ == _); last by done.
              move: EQ => /eqP EQ. rewrite /n -EQ.
              case INT: (_ <= _ < _); last by done.
              apply eq_leq; symmetry; apply/eqP; rewrite eqb1.
              move: INT => /andP [GEt LTt].
              rewrite (same_service_in_suspension_interval _ _ _ _ t') //.
              {
                rewrite -/b [b t'](same_service_implies_same_last_execution  _ _ t);
                  last by rewrite SERV EQ.
                by apply/andP; split.
              }
              {
                rewrite /suspension_duration -/b.
                rewrite [b t'](same_service_implies_same_last_execution _ _ t);
                  last by rewrite SERV EQ.
                by apply/andP; split; last by apply ltnW.
              }
            }
            apply leq_trans with (n := \sum_(b t' <= t < b t' + n) 1);
              last by simpl_sum_const; rewrite addKn.
            by apply leq_sum1_smaller_range; move => i [LE LE']; split.
          }
        Qed.

      End BoundOnCumulativeSuspension.
      
      (* Next, we show that when a job completes, it must have suspended
         as long as the total suspension time. *)
      Section SuspendsForTotalSuspension.

        (* Assume that jobs do not execute before they arrive... *)
        Hypothesis H_jobs_must_arrive_to_execute:
          jobs_must_arrive_to_execute sched.

        (* ...and nor after completion. *)
        Hypothesis H_completed_jobs_dont_execute:
          completed_jobs_dont_execute job_cost sched.
      
        (* Assume that the schedule respects self-suspensions. *)
        Hypothesis H_respects_self_suspensions: respects_self_suspensions.

        (* Let j be any job in the arrival sequence. *)
        Variable j: JobIn arr_seq.

        (* Assume that j has completed by time t. *)
        Variable t: time.
        Hypothesis H_j_has_completed: completed_by job_cost sched j t.

        (* Then, we prove that the cumulative suspension time must be
           exactly equal to the total suspension time of the job. *)
        Lemma cumulative_suspension_eq_total_suspension:
          cumulative_suspension j t = total_suspension job_cost next_suspension j.
        Proof.
          rename H_j_has_completed into COMP, H_jobs_must_arrive_to_execute into ARR.
          have EARLIER := exists_last_execution_with_smaller_service j ARR t COMP.
          apply/eqP; rewrite eqn_leq; apply/andP; split;
            first by apply cumulative_suspension_le_total_suspension.
          rewrite /total_suspension /cumulative_suspension /cumulative_suspension_during.
          move: COMP => /eqP COMP.
          apply leq_trans with (n := \sum_(0 <= s < job_cost j)
                                      \sum_(0 <= t0 < t | service sched j t0 == s) suspended_at j t0);
            last first.
          {
            rewrite (exchange_big_dep_nat (fun x => true)) //=.
            apply leq_sum_nat; move => t0 /andP [_ LT] _.
            case (boolP [exists s: 'I_(job_cost j), service sched j t0 == s]) => [EX | ALL].
            {
              move: EX => /existsP [s /eqP EQs].
              rewrite big_mkcond /=.
              rewrite (bigD1_seq (nat_of_ord s)); [simpl | | by apply iota_uniq];
                last by rewrite mem_index_iota; apply/andP;split; last by apply ltn_ord.
              rewrite EQs eq_refl big1; first by rewrite addn0.
              by move => i /negbTE NEQ; rewrite eq_sym NEQ.
            }
            {
              rewrite big_nat_cond big1; first by done.
              move => i /andP [/andP [_ LTi] /eqP SERV].
              rewrite negb_exists in ALL; move: ALL => /forallP ALL.
              by specialize (ALL (Ordinal LTi)); rewrite /= SERV eq_refl in ALL.
            }
          }
          {
            apply leq_sum_nat; move => s /andP [_ LTs] _.
            rewrite /suspended_at /suspension_duration.
            set b := time_after_last_execution j.
            set n := next_suspension j.

            move: (EARLIER s LTs) => [t' EQ'].
            apply leq_trans with (n := \sum_(0 <= t0 < t | (service sched j t0 == s) &&
                                        (b t' <= t0 < b t' + n (service sched j (b t')))) 1); last first.
            {
              rewrite big_mkcond [\sum_(_ <= _ < _ | _ == s)_]big_mkcond.
              apply leq_sum_nat; move => i /andP [_ LTi] _.
              case EQi: (service sched j i == s); [rewrite andTb | by rewrite andFb].
              case LE: (_ <= _ <= _); last by done.
              rewrite lt0n eqb0 negbK.
              apply suspended_in_suspension_interval with (t := t'); try (by done).
              rewrite neq_ltn; apply/orP; left.
              by apply: (leq_ltn_trans _ LTs); apply eq_leq; apply/eqP.
            }
            {
              apply leq_trans with (n := \sum_(b t' <= t0 < b t' + n (service sched j (b t')) |
                                               (0 <= t0 < t) && (service sched j t0 == s)) 1).
              {
                apply leq_trans with (n := \sum_(b t' <= t0 < b t' + n (service sched j (b t'))) 1);
                  first by simpl_sum_const; rewrite addKn -EQ'.
                rewrite [in X in _ <= X]big_mkcond /=.
                apply leq_sum_nat; move => i /andP [LEi GTi] _.
                apply eq_leq; symmetry; apply/eqP; rewrite eqb1.
                apply/andP; split.
                {
                  have SUSPi: suspended_at j i.
                  {
                    apply: (suspended_in_suspension_interval _ _ _ _ t');
                      try (by done); last by apply/andP; split.
                    rewrite neq_ltn; apply/orP; left.
                    rewrite (same_service_in_suspension_interval _ _ _ _ t') //;
                      first by rewrite EQ'.
                    by apply/andP; split; last by apply ltnW.
                  }
                  apply contraT; rewrite -leqNgt; intro LE.
                  apply suspended_implies_not_completed in SUSPi.
                  exfalso; move: SUSPi => /negP COMPi; apply COMPi.
                  apply completion_monotonic with (t0 := t); try (by done).
                  by apply/eqP.
                }
                {
                  rewrite -EQ'; apply/eqP.
                  apply same_service_in_suspension_interval; try (by done).
                  by apply/andP; split; last by apply ltnW.
                }
              }
              {
                apply leq_sum1_smaller_range.
                by move => i [LEb /andP [LE EQs]]; split;
                  last by apply/andP; split.
              }
            }
          }
        Qed.
        
      End SuspendsForTotalSuspension.

    End Lemmas.
      
  End DefiningSuspensionIntervals.

End SuspensionIntervals.