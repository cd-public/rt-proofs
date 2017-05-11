Require Import rt.util.all.
Require Import rt.model.time rt.model.arrival.basic.job rt.model.arrival.basic.task rt.model.arrival.basic.arrival_sequence rt.model.priority.
Require Import rt.model.schedule.uni.schedule rt.model.schedule.uni.schedulability rt.model.schedule.uni.basic.platform.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.


Module TotalService.

  Import UniprocessorSchedule Schedulability Platform Job.

  (* In this section, we prove some useful lemmas about total_service. *)
  Section Lemmas.

    Context {Task: eqType}.
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_deadline: Job -> time.
    Variable job_task: Job -> Task.

    (* Consider any job arrival sequence with consistent, duplicate-free arrivals... *)
    Context {arr_seq: arrival_sequence Job}.
    Hypothesis H_arrival_sequence_is_a_set:
      arrival_sequence_is_a_set arr_seq.
    Hypothesis H_arrival_sequence_is_consistent:
      arrival_times_are_consistent job_arrival arr_seq.

    (* ... and any schedule of this arrival sequence.... *)
    Variable sched: schedule Job.
    Hypothesis H_jobs_come_from_arrival_sequence: jobs_come_from_arrival_sequence sched arr_seq.

    (* ...where jobs must arrive to execute. *)
    Hypothesis H_jobs_must_arrive_to_execute:
      jobs_must_arrive_to_execute job_arrival sched.

    Section HelperLemmas.

      (* TEMPORARY: These should be moved to the correct files. *)
      Lemma jobs_arrived_between_single:
        forall t,
          jobs_arrived_between arr_seq t t.+1 = jobs_arriving_at arr_seq t.
      Proof.
        by intros t; rewrite /jobs_arrived_between big_nat_recr //= big_geq //.
      Qed.

      Lemma all_filter_neg:
        forall {T: eqType} a (s: seq T),
          all (predC a) s = (filter a s == [::]).
      Proof.
        intros T a s.
        apply/idP/idP; first by rewrite -[_==_]negbK -has_filter -all_predC.
        move => /eqP EQ.
        apply contraT; rewrite -has_predC; move => /hasP [x IN] /= A.
        suff BUG: x \in [::] by rewrite in_nil in BUG.
        rewrite -EQ mem_filter IN andbT.
        by apply contraT; intro BUG; rewrite BUG in A.
      Qed.

      Lemma jobs_arrived_between_cat:
        forall t_mid t1 t2,
          t1 <= t_mid ->
          t_mid <= t2 ->
          jobs_arrived_between arr_seq t1 t2 =
          jobs_arrived_between arr_seq t1 t_mid ++ jobs_arrived_between arr_seq t_mid t2.
      Proof.
        rewrite /jobs_arrived_between.
        induction t_mid.
        {
          intros t1 t2 EQ0 _.
          rewrite leqn0 in EQ0; move: EQ0 => /eqP <-.
          by rewrite [X in _ = X ++ _]big_geq.
        }
        {
          intros t1 t2 GE LT.
          rewrite leq_eqVlt in GE; move: GE => /orP [/eqP EQ | GT];
            first by rewrite -EQ [X in _ = X ++ _]big_geq.
          rewrite big_nat_recr //=.
          rewrite IHt_mid //; last by apply ltnW.
          rewrite -catA; f_equal.
          destruct t2; first by rewrite ltn0 in LT.
          rewrite big_nat_recl //; f_equal.
          by rewrite big_add1.
        }
      Qed.

    End HelperLemmas.
    
    Lemma busy_last_instant:
      forall t d,
        \sum_(j <- jobs_arrived_before arr_seq (t + d).+1) service_during sched j t (t + d).+1
        = (\sum_(j <- jobs_arrived_before arr_seq (t + d)) service_during sched j t (t + d)
            + ~~ is_idle sched (t + d)).
    Proof.
      intros t d.
      rewrite /service_during exchange_big [X in _ = X + _]exchange_big /=.
      rewrite big_nat_recr ?leq_addr //=.
      destruct (sched (t+d)) as [j'|] eqn:SCHED; rewrite /is_idle SCHED /= ?addn0.
      {
        move: SCHED => /eqP SCHED; rewrite -/(scheduled_at sched j' (t+d)) in SCHED.
        rewrite [X in _ + X = _](bigD1_seq j') /=; last by eapply arrivals_uniq; eauto 1.
        {
          rewrite [\sum_(_ <- _ arr_seq _ | _)_]big1 ?addn0; last first.
          {
            intros i NEQ; apply/eqP; rewrite eqb0; apply/negP; intro SCHEDi.
            by apply only_one_job_scheduled with (j1 := i) in SCHED; first by rewrite SCHED eq_refl in NEQ.
          }
          f_equal; last by rewrite /service_at SCHED.
          apply eq_big_nat; move => i /andP [GE LT].
          rewrite -big_mkcond -[X in _ = X]big_mkcond /=.
          rewrite -big_filter -[X in _ = X]big_filter.
          apply congr_big; try done.
          rewrite /jobs_arrived_before (jobs_arrived_between_cat (t+d)) //.
          rewrite jobs_arrived_between_single filter_cat.
          set l := (X in _ ++ X = _).
          suff EMPTY: l = [::] by rewrite EMPTY cats0.
          apply/eqP; rewrite -all_filter_neg.          
          apply/allP; move => j IN /=; apply/negP; intro SCHEDi.
          apply H_arrival_sequence_is_consistent in IN.
          suff BUG: i < i by rewrite ltnn in BUG.
          apply: (leq_trans LT); rewrite -IN.
          by apply H_jobs_must_arrive_to_execute.
        }
        {
          apply: arrived_between_implies_in_arrivals; first by apply H_arrival_sequence_is_consistent. 
          - by eapply H_jobs_come_from_arrival_sequence, SCHED.
          - by rewrite /arrived_between /= ltnS; apply H_jobs_must_arrive_to_execute.
        }
      }
      {
        rewrite [X in _ + X = _]big1 ?addn0;
          last by intros j _; rewrite /service_at /scheduled_at SCHED.
        rewrite big_nat_cond [X in _ = X]big_nat_cond.
        apply eq_bigr; move => i /andP [/andP [GE LT] _].
        rewrite /jobs_arrived_before (jobs_arrived_between_cat (t+d)) //.
        rewrite big_cat /= jobs_arrived_between_single.
        rewrite [X in _ + X = _]big1_seq ?addn0; first by done.
        move => j /= IN.
        apply/eqP; rewrite eqb0; apply/negP; intro SCHEDi.
        apply H_jobs_must_arrive_to_execute in SCHEDi.
        apply H_arrival_sequence_is_consistent in IN.
        suff BUG: t + d < t + d by rewrite ltnn in BUG.
        by apply: (leq_ltn_trans _ LT); rewrite -IN.
      }
    Qed.

    (* The total service provided is bounded by the length of the interval. *)
    Lemma total_service_bounded_by_interval_length:
      forall (t:time) (d:time), total_service_during sched t (t + d) <= d.
    Proof.
      intros t d. elim d.
      unfold total_service_during. replace (t+0) with t; auto.
      rewrite [\sum_(t <= t0 < t)_]big_geq. auto. auto.
      move => n. intros IH.
      unfold total_service_during. nat_norm.
      rewrite [\sum_(t <= t0 < (t+n).+1)_]big_nat_recr. Focus 2. apply leq_addr.
      replace (\big[addn_monoid/0]_(t <= i < t + n)_) with (total_service_during sched t (t+n)); auto.
      case_eq(~~ is_idle sched (t+n)); intros CaseH.
      rewrite -> addn1. apply IH.
      rewrite -> addn0. rewrite -> leqW. auto. apply IH.
      Qed.

    (* The total service during an interval is the sum of service
       of all jobs that arrive before the end of the interval. *)
    Lemma sum_of_service_of_jobs_is_total_service:
      forall (t:time) (d:time), total_service_during sched t (t+d) =
                                \sum_(j <- (jobs_arrived_before arr_seq (t+d))) service_during sched j t (t + d).
    Proof.
      intros t.
      unfold total_service_during in *.
      induction d.
      replace (t+0) with t by trivial.
      rewrite [\sum_(t <= t0 < t)_]big_geq; trivial.
      unfold service_during in *.
      rewrite [\sum_(j <- jobs_arrived_before arr_seq t)
                \sum_(t <= t0 < t)_]exchange_big.
      rewrite [\big[addn_comoid/0]_(t <= j < t)_]big_geq; auto; auto.
      rewrite -> big_cat_nat with (n := t+d);
        [> | apply leq_addr | nat_norm; apply leqnSn].
      unfold jobs_must_arrive_to_execute in *.
      rewrite -> big_cat_nat with (n := t+d) in IHd;
        [> | apply leq_addr | auto].
      rewrite [\big[addn_monoid/0]_(t + d <= i < t + d)_]big_geq in IHd; auto. 
      rewrite -> addn0 in IHd.
      rewrite -> IHd. nat_norm.
      rewrite[\big[addn_monoid/0]_(t + d <= i < (t + d).+1)_]big_nat1.
      
      case_eq (~~ is_idle sched (t + d)). intro H.
      replace (addn_monoid (\sum_(j <- jobs_arrived_before arr_seq (t + d))
                             service_during sched j t (t + d)) (nat_of_bool true))
        with
          (addn_monoid (\sum_(j <- jobs_arrived_before arr_seq (t + d))
                         service_during sched j t (t + d)) 1); auto. symmetry.
      (*
      apply busy_last_instant; apply H.
      intro H.
      replace (addn_monoid (\sum_(j <- jobs_arrived_before arr_seq (t + d))
                             service_during sched j t (t + d)) (nat_of_bool false))
        with
          (addn_monoid (\sum_(j <- jobs_arrived_before arr_seq (t + d))
                         service_during sched j t (t + d)) 0); auto. symmetry.
      apply idle_last_instant. rewrite -> negbFE; [auto | apply H].
      Qed.*)
      Admitted.

  End Lemmas.

End TotalService.