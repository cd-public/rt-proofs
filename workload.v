Require Import Classical Vbase job task schedule task_arrival response_time
        schedulability divround helper priority identmp
        ssreflect ssrbool eqtype ssrnat seq div fintype bigop ssromega.

Section WorkloadBound.
  
(* Workload is defined as the total service received by jobs of
   a specific task in the interval [t,t'). *)
Definition workload (sched: schedule) (ts: taskset) (tsk: sporadic_task) (t t': time) :=
  \sum_(j <- prev_arrivals sched t' | job_of tsk j) (service_during sched j t t').

Definition max_jobs (tsk: sporadic_task) (R_tsk: time) (delta: time) :=
  div_floor (delta + R_tsk - task_cost tsk) (task_period tsk).

Definition W (tsk: sporadic_task) (R_tsk: time) (delta: time) :=
  let n_k := (max_jobs tsk R_tsk delta) in
  let e_k := (task_cost tsk) in
  let d_k := (task_deadline tsk) in
  let p_k := (task_period tsk) in            
    minn e_k (delta + R_tsk - e_k - n_k * p_k) + n_k * e_k.

(* A carried-in job in [t1,t2) arrives before t1 and is not completed at time t1 *)
Definition carried_in (sched: schedule) (tsk: sporadic_task) (t1: time) (j: job) :=
  [&& job_task j == tsk, arrived_before sched j t1 & ~~ completed sched j t1].

(* A carried-out job in [t1,t2) arrives after t1 and is not completed at time t2 *)
Definition carried_out (sched: schedule) (tsk: sporadic_task) (t1 t2: time) (j: job) :=
  [&& job_task j == tsk, arrived_between sched j t1 t2 & ~~ completed sched j t2].


Lemma workload_bound :
  forall ts sched (ARRts: ts_arrival_sequence ts sched)
         hp cpumap num_cpus (MULT: ident_mp num_cpus hp cpumap sched) 
         (RESTR: restricted_deadline_model ts)
         tsk (IN: tsk \in ts) j (JOB: job_task j = tsk)
         arr_j (ARRj: arrives_at sched j arr_j)
         (SCHED: task_misses_no_deadlines sched ts tsk)
         R_tsk (RESP: task_response_time_ub tsk ts R_tsk),
    (workload sched ts tsk arr_j (arr_j + job_deadline j)) <= W tsk R_tsk (job_deadline j).
Proof.
  unfold workload, W; ins.
  remember (max_jobs tsk R_tsk (job_deadline j)) as n_k.
  remember (prev_arrivals sched (arr_j + job_deadline j)) as released_jobs.
  remember (count (fun x => job_of tsk x &&
                            (service_during sched x arr_j (arr_j + job_deadline j) != 0))
              released_jobs) as num_jobs.
  destruct (num_jobs <= n_k) eqn:NUM.
  {
    rewrite -[\sum_(_ <- _ | _) _]add0n leq_add //.
    rewrite (bigID (fun x => service_during sched x arr_j (arr_j + job_deadline j) == 0)) /=.
    rewrite (eq_bigr (fun x => 0)); last by (intro j_i; move/andP; ins; des; by apply/eqP).
    rewrite big_const_seq iter_addn mul0n add0n add0n.
    apply leq_trans with (n := \sum_(x <- released_jobs | (job_of tsk x) &&
                                    (service_during sched x arr_j (arr_j + job_deadline j) != 0))
                                task_cost tsk);
    last by rewrite big_const_seq iter_addn addn0 mulnC -Heqnum_jobs leq_mul2r; apply/orP; right.
    {
      apply leq_sum; unfold job_of; intros j_i; move/andP => JOBi; des.
      have PROP := job_properties j_i; des.
      apply leq_trans with (n := job_cost j_i);
        last by unfold beq_task in *; destruct task_eq_dec as [EQ|]; try rewrite -EQ; ins.
      by apply service_interval_max_cost; unfold ident_mp in MULT; des.
    }
  }
  {
    (* Hard case: num_jobs with service > 0 in the interval is larger than n_k *)
    assert (NUM_EQ: num_jobs = n_k + 1). admit. clear NUM.

    admit.
  }
Qed.

  
(*Lemma carried_in_unique :
  forall ts sched (ARRts: ts_arrival_sequence ts sched)
         (RESTR: restricted_deadline_model ts)
         tsk (IN: tsk \in ts) j (JOB: job_task j = tsk)
         arr (ARRj: arrives_at sched j arr)
         (SCHED: task_misses_no_deadlines sched ts tsk),
    let released_jobs := prev_arrivals sched (arr + job_deadline j) in
      (exists j_in, << CARRY: carried_in sched tsk arr j_in >> /\
                    << FILTER: filter (carried_in sched tsk arr) released_jobs = [::j_in] >>) \/
      << FILTER: filter (carried_in sched tsk arr) released_jobs = nil >>.
Proof.
Admitted.

Lemma carried_out_unique :
  forall ts sched (ARRts: ts_arrival_sequence ts sched)
         (RESTR: restricted_deadline_model ts)
         tsk (IN: tsk \in ts) j (JOB: job_task j = tsk)
         arr (ARRj: arrives_at sched j arr)
         (SCHED: task_misses_no_deadlines sched ts tsk),
  let released_jobs := prev_arrivals sched (arr + job_deadline j) in
    (exists j_out, << CARRY: carried_out sched tsk arr (arr + job_deadline j) j_out >> /\
                   << FILTER: filter (carried_out sched tsk arr (arr + job_deadline j))
                                released_jobs = [::j_out] >>) \/
    << FILTER: filter (carried_out sched tsk arr (arr + job_deadline j))
                 released_jobs = nil >>.
Proof.
Admitted.

Lemma workload_bound :
  forall ts sched (ARRts: ts_arrival_sequence ts sched)
         hp cpumap num_cpus (MULT: ident_mp num_cpus hp cpumap sched) 
         (RESTR: restricted_deadline_model ts)
         tsk (IN: tsk \in ts) j (JOB: job_task j = tsk)
         arr_j (ARRj: arrives_at sched j arr_j)
         (SCHED: task_misses_no_deadlines sched ts tsk)
         R_tsk (RESP: task_response_time_ub tsk ts R_tsk),
    (workload sched ts tsk arr_j (arr_j + job_deadline j)) <= W tsk R_tsk (job_deadline j).
Proof.
  unfold workload; ins.
  remember (prev_arrivals sched (arr_j + job_deadline j)) as released_jobs.
  rewrite (bigID (carried_out sched tsk arr_j (arr_j + job_deadline j))); simpl.
  apply leq_add.
  {
    rewrite -> eq_bigl with (P2 := fun x => carried_out sched tsk arr_j (arr_j + job_deadline j) x);
      last (
        by unfold ssrfun.eqfun, carried_out, job_of; ins;
        rewrite andb_idl //; move/and3P => CARRYjob; destruct CARRYjob).
    generalize SCHED; apply carried_out_unique with (j := j) (arr := arr_j) in SCHED; des; ins;
    rewrite <- Heqreleased_jobs in *;
    [rewrite -big_filter FILTER big_cons big_nil addn0 | by rewrite -big_filter FILTER big_nil //].

    rewrite leq_min; apply/andP; split.
    { 
      move: CARRY => /and3P CARRY; destruct CARRY as [JOB_out _ _].
      move: JOB_out => /eqP JOB_out; rewrite -JOB_out.
      have PROP := job_properties j_out; des.
      apply leq_trans with (n := job_cost j_out); [|by ins].
      by apply service_interval_max_cost; [by unfold ident_mp in *; des].
    }
    {
      move: CARRY => /and3P CARRY; destruct CARRY as [_ ARRout _]; unfold arrived_between in *.
      move: ARRout => /exists_inPQ_nat ARRout. destruct ARRout as [arr_out [LTout [GEout _]]].
      unfold service_during.
      assert (SUM: \sum_(arr_j <= t < arr_j + job_deadline j) service_at sched j_out t =
                   \sum_(arr_j <= t < arr_out) service_at sched j_out t + 
                   \sum_(arr_out <= t < arr_j + job_deadline j) service_at sched j_out t). admit.
      rewrite SUM.
      assert (ZERO: \sum_(arr_j <= t < arr_out) service_at sched j_out t = 0).  admit.
      rewrite ZERO add0n.
      apply leq_trans with (n := \sum_(arr_out <= t < arr_j + job_deadline j) 1).
        by apply leq_sum; unfold ident_mp in *; des; ins; rewrite mp_max_service.
      rewrite big_const_nat iter_addn addn0 mulnC muln1.
      rewrite addnC -subnBA //.
      
      (* Prove that service of t_0 + delta - arrival time of j_out <= (delta + R_k - e_k) % p_k *) 

      generalize SCHED; apply carried_in_unique with (j := j) (arr := arr_j) in SCHED; des; ins;
      rewrite <- Heqreleased_jobs in *.
      move: CARRY => /and3P CARRY; destruct CARRY as [_ ARRin _]; unfold arrived_before in *.
      move: ARRin => /exists_inP_nat ARRin; destruct ARRin as [arr_in [LTin ARRin]].

      assert (EXk: arr_out >= arr_in + div_floor (arr_out - arr_in) (task_period tsk)). admit.
      rewrite EXk.
      admit. admit.
    }
  }
  {
    rewrite big_seq_cond.
    apply leq_trans with
    (n := \sum_(i <- released_jobs | [&& (i \in released_jobs),
          job_of tsk i & ~~ carried_out sched tsk arr_j
                             (arr_j + job_deadline j) i]) task_cost tsk).
    {
      apply leq_sum; unfold job_of; intros j_i.
      move/and3P => INj_i; destruct INj_i.
      unfold beq_task in *; destruct task_eq_dec as [JOBi|]; ins.
      have PROP := job_properties j_i; des.
      apply leq_trans with (n := job_cost j_i); [|by rewrite -JOBi].
      apply service_interval_max_cost.
      by unfold ident_mp in MULT; des.
    }
    {
      rewrite big_const_seq iter_addn addn0 mulnC.
      rewrite leq_mul2r.
      apply/orP; right.
      unfold max_jobs.
      (* Prove that number of jobs minus carried-out <= n_k *)
      admit.
    }
  }
Qed.
*)
End WorkloadBound.