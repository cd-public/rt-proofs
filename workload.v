Require Import Vbase job task schedule task_arrival response_time
               schedulability util_divround util_lemmas
               ssreflect ssrbool eqtype ssrnat seq div fintype bigop path.

Module Workload.

  Import Job SporadicTaskset Schedule SporadicTaskArrival ResponseTime Schedulability.

  (* Let's define the workload. *)
  Section WorkloadDef.

    Context {sporadic_task: eqType}.
    Context {Job: eqType}.
    Variable job_task: Job -> sporadic_task.
    Context {arr_seq: arrival_sequence Job}.
    
    Context {num_cpus: nat}.
    Variable rate: Job -> processor num_cpus -> nat.
    Variable sched: schedule num_cpus arr_seq.

    (* Consider some task *)
    Variable tsk: sporadic_task.

    (* First, we define a function that returns the amount of service
       received by this task in a particular processor. *)
    Definition service_of_task (cpu: processor num_cpus)
                               (j: option (JobIn arr_seq)) :=
      match j with
        | Some j' => (job_task j' == tsk) * (rate j' cpu)
        | None => 0
      end.

    (* Next, workload is defined as the service received by jobs of
       the task in the interval [t1,t2). *)
    Definition workload (t1 t2: time) :=
      \sum_(t1 <= t < t2)
        \sum_(cpu < num_cpus)
          service_of_task cpu (sched cpu t).

    
    (* Now, we define workload by summing up the cumulative service
       during [t1,t2) of the scheduled jobs, but only those spawned
       by the task that we care about. *)
    Definition workload_joblist (t1 t2: time) :=
      \sum_(j <- jobs_scheduled_between sched t1 t2 | job_task j == tsk)
        service_during rate sched j t1 t2.

    (* ??? *)
    Lemma scheduled_between_helper :
      forall j t,
        (forall cpu t, rate cpu t > 0) ->
        (j \in \big[cat/[::]]_(cpu < num_cpus) make_sequence (sched cpu t))
          = (service_at rate sched j t != 0).
    Proof.
      unfold service_at; intros j t RATE.
      rewrite [\sum_(_ < _ | _) _]big_mkcond.
      destruct num_cpus; first by rewrite 2!big_ord0 in_nil.
      assert (LT0: 0 < n.+1); first by done.
      rewrite (big_nth (Ordinal LT0)).
      rewrite (big_nth (Ordinal LT0)).
      set m := size (index_enum (ordinal_finType n.+1)).
      induction m; first by rewrite big_geq // big_geq //.
      {
        rewrite big_nat_recr; last by done.
        rewrite big_nat_recr; last by done.
        rewrite mem_cat.
        rewrite IHm.
        destruct ( (j
         \in make_sequence
               (sched
                  (nth (Ordinal (n:=n.+1) (m:=0) LT0)
                       (index_enum (ordinal_finType n.+1)) m) t))) eqn: SUBST.
        {
          rewrite orbT.
          unfold make_sequence in SUBST.
          destruct (sched (nth (Ordinal LT0) (index_enum (ordinal_finType n.+1)) m) t); last by done.
          rewrite mem_seq1 in SUBST.
          move: SUBST => /eqP SUBST; subst.
          rewrite eq_refl.
          symmetry; rewrite -lt0n.
          apply leq_trans with (0 + 1); first by done.
          apply leq_add; first by done.
          by rewrite RATE.
        }
        {
          unfold make_sequence in SUBST.
          destruct (sched (nth (Ordinal LT0) (index_enum (ordinal_finType n.+1)) m ) t).
          {
            rewrite mem_seq1 in SUBST.
            destruct (Some j0 == Some j) eqn:SOME.
            {
              move: SOME SUBST => /eqP SOME /eqP SUBST; inversion SOME. rewrite H0 in SUBST. by done.
            }
            {
              rewrite SOME. rewrite orbF. simpl. rewrite addn0.
              ins.
            }
          }
          {
            desf. rewrite orbF /= addn0. ins.
          }
        }
      }
    Qed.

    (* If a job i scheduled in an time interval, it will get service in this interval. *)
    Lemma scheduled_between_implies_service :
      forall j t1 t2,
        (forall j cpu, rate j cpu > 0) ->
        (j \in jobs_scheduled_between sched t1 t2) =
        (service_during rate sched j t1 t2 != 0).
    Proof.
      intros j t1 t2 RATE; unfold service_during; rewrite mem_undup.
      induction t2;
        first by rewrite 2?big_geq //.      
      destruct (leqP t1 t2) as [LE | GT]; last by rewrite 2?big_geq //.
      unfold service_during; rewrite 2?big_nat_recr ?mem_cat /= //.
      rewrite IHt2.
      destruct (\sum_(t1 <= t < t2) service_at rate sched j t);
        last by done.
      rewrite eq_refl orFb add0n.
      by apply scheduled_between_helper, RATE.
    Qed.

    (* Next, we show that the two definitions are equivalent. *)
    Lemma workload_eq_workload_joblist :
      forall t1 t2,
      workload t1 t2 = workload_joblist t1 t2.
    Proof.
      intros t1 t2; unfold workload, workload_joblist, service_during.
      rewrite [\sum_(j <- jobs_scheduled_between _ _ _ | _) _]exchange_big /=.
      apply eq_big_nat; unfold service_at; intros t LEt.
      rewrite [\sum_(i <- jobs_scheduled_between _ _ _ | _) _](eq_bigr (fun i =>
               \sum_(cpu < num_cpus) (sched cpu t == Some i) * rate i cpu));
        last by ins; rewrite big_mkcond; apply eq_bigr; ins; rewrite mulnbl.
      rewrite exchange_big /=; apply eq_bigr.
      intros cpu LEcpu; rewrite -big_filter.
      destruct (sched cpu t) eqn:SCHED; simpl; last first.
        by rewrite -> eq_bigr with (F2 := fun i => 0);
          [by rewrite big_const_seq iter_addn | by ins].
        {
          destruct (job_task j == tsk) eqn:EQtsk;
            try rewrite mul1n; try rewrite mul0n.
          {  
            rewrite -> bigD1_seq with (j := j); last by rewrite filter_undup undup_uniq.
            { 
              rewrite -> eq_bigr with (F2 := fun i => 0);
                first by rewrite big_const_seq iter_addn /= mul0n 2!addn0 eq_refl mul1n.
                intros i NEQ; destruct (Some j == Some i) eqn:SOMEeq; last by rewrite SOMEeq mul0n.
                by move: SOMEeq => /eqP SOMEeq; inversion SOMEeq; subst; rewrite eq_refl in NEQ.
            }
            {
              rewrite mem_filter; apply/andP; split; first by ins.
              rewrite mem_undup.
              apply mem_bigcat_nat with (j := t); first by ins.
              apply mem_bigcat_ord with (j := cpu); first by apply ltn_ord.
              by rewrite SCHED inE; apply/eqP.
            }
          }
          {
            rewrite big_filter; rewrite -> eq_bigr with (F2 := fun i => 0);
              first by rewrite big_const_seq iter_addn mul0n addn0.
            intros i EQtsk2; destruct (Some j == Some i) eqn:SOMEeq; last by rewrite mul0n.
            by move: SOMEeq => /eqP SOMEeq; inversion SOMEeq;
              subst; rewrite EQtsk2 in EQtsk.
          }
        }
      Qed.
 
  End WorkloadDef.
End Workload.
