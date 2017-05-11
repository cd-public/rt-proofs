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

    (* Consider any job arrival sequence with no duplicate jobs... *)
    Context {arr_seq: arrival_sequence Job}.
    Hypothesis H_arrival_sequence_is_a_set:
      arrival_sequence_is_a_set arr_seq.

    (* ... and any schedule of this arrival sequence. *)
    Variable sched: schedule Job.

    (* Assume that jobs only execute after they arrived. *)
    Hypothesis H_jobs_must_arrive_to_execute:
      jobs_must_arrive_to_execute job_arrival sched.
    Hypothesis H_arr_seq_gives_job_arrival:
      forall j t, j \in arr_seq t <-> job_arrival j = t.

    (* added hypothesis. need to fix.*)
    Lemma busy_last_instant:
      forall t d,  ( \sum_(j <- jobs_arrived_before arr_seq (t + d).+1)
                      service_during sched j t (t + d).+1)
                   = ((\sum_(j <- jobs_arrived_before arr_seq (t + d))
                        service_during sched j t (t + d)) + (~~ is_idle sched (t + d))).
    Proof.
      unfold service_during, service_at, scheduled_at, jobs_arrived_before, arrived_between; intros t d.
      replace (jobs_arrived_between arr_seq 0 (t + d).+1) with (jobs_arrived_between arr_seq 0 (t + d) ++ jobs_arriving_at arr_seq (t + d)).
      Focus 2.
      unfold jobs_arrived_between.
      rewrite big_nat_recr; auto.
      replace (jobs_arrived_between arr_seq 0 (t + d).+1) with (jobs_arrived_between arr_seq 0 (t + d) ++ jobs_arriving_at arr_seq (t + d)).
      rewrite -> big_cat.
      rewrite -> exchange_big.
      rewrite -> big_cat_nat with (n := t + d).
      unfold is_idle.
      replace (\big[addn_comoid/0]_(t <= i < t + d) \big[addn_comoid/0]_(i0 <- jobs_arrived_between arr_seq 0 (t + d))(sched i == Some i0)) with (\sum_(j <- jobs_arrived_between arr_seq 0 (t + d)) \sum_(t <= t0 < t + d) (sched t0 == Some j)).
      Focus 2.
      rewrite -> exchange_big; auto.
      Focus 4.
      unfold jobs_arrived_between.
      symmetry.
      rewrite -> big_nat_recr; auto.
      Focus 2.
      apply leq_addr.
      Focus 2.
      apply leqnSn with (n := (t + d)).
      replace (\big[addn_comoid/0]_(t + d <= i < (t + d).+1) \big[addn_comoid/0]_(i0 <- jobs_arrived_between arr_seq 0 (t + d)) (sched i == Some i0)) with (\big[addn_comoid/0]_(i0 <- jobs_arrived_between arr_seq 0 (t + d))(sched (t + d) == Some i0)).
      Focus 2.
      symmetry.
      rewrite -> big_nat1; auto.
      replace (\big[addn_monoid/0]_(i <- jobs_arriving_at arr_seq (t + d))(\sum_(t <= t0 < (t + d).+1) (sched t0 == Some i))) with (\big[addn_monoid/0]_(i <- jobs_arriving_at arr_seq (t + d))(sched (t + d) == Some i)).
      Focus 2.
      symmetry.
      rewrite -> exchange_big.
      rewrite -> big_cat_nat with (n := t + d).
      replace (\big[addn_comoid/0]_(t + d <= i < (t + d).+1) \big[addn_comoid/0]_(i0 <- jobs_arriving_at arr_seq (t + d)) (sched i == Some i0)) with (\big[addn_monoid/0]_(i <- jobs_arriving_at arr_seq (t + d)) (sched (t + d) == Some i)).
      Focus 2.
      symmetry.
      rewrite -> big_nat1.
      auto.
      Focus 2.
      apply leq_addr.
      Focus 2.
      apply leqnSn with (n := (t + d)).
      replace (\big[addn_comoid/0]_(t <= i < t + d) \big[addn_comoid/0]_(i0 <- jobs_arriving_at arr_seq (t + d)) (sched i == Some i0)) with 0.
      auto.
      unfold jobs_must_arrive_to_execute, scheduled_at, has_arrived in H_jobs_must_arrive_to_execute.
      unfold jobs_arriving_at.
      symmetry.
      
    Admitted.

    (* added hypothesis. need to fix.*)
    Lemma idle_last_instant:
      forall t d,  (is_idle sched (t + d)) 
      ->   ( \sum_(j <- jobs_arrived_before arr_seq (t + d).+1)
      service_during sched j t (t + d).+1)
            =   ((\sum_(j <- jobs_arrived_before arr_seq (t + d))
                   service_during sched j t (t + d)) + 0).
    Proof.
      Admitted.

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