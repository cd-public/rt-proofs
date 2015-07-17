Require Import Classical Vbase job task schedule task_arrival
        schedulability divround helper priority identmp
        ssreflect ssrbool eqtype ssrnat seq div fintype bigop ssromega.

Section WorkloadBound.
  
(* Workload is defined as the total service received by jobs of
   a specific task in the interval [t,t'). *)
Definition workload (sched: schedule) (ts: taskset) (tsk: sporadic_task) (t t': time) :=
  \sum_(j <- prev_arrivals sched t' | job_of tsk j) (service_during sched j t t').

Definition max_jobs (tsk: sporadic_task) (delta: time) :=
  div_floor (delta + task_deadline tsk - task_cost tsk) (task_period tsk).

Definition W (tsk: sporadic_task) (delta: time) :=
  let n_k := (max_jobs tsk delta) in
  let e_k := (task_cost tsk) in
  let d_k := (task_deadline tsk) in
  let p_k := (task_period tsk) in            
    minn e_k (delta + d_k - e_k - n_k * p_k) + n_k * e_k.

Definition carried_in (sched: schedule) (tsk: sporadic_task) (t: time) (j: job) :=
  [&& job_task j == tsk, arrived sched j (t - 1) & ~~ completed sched j t].

Lemma carried_in_unique :
  forall ts sched (ARRts: ts_arrival_sequence ts sched)
         (RESTR: restricted_deadline_model ts)
         tsk (IN: tsk \in ts) j (JOB: job_task j = tsk)
         arr (ARRj: arrives_at sched j arr)
         (SCHED: task_misses_no_deadlines sched ts tsk),
    let released_jobs := prev_arrivals sched (arr + job_deadline j) in
      (exists j_0, << CARRY: carried_in sched tsk arr j_0 >> /\
                   << FILTER: filter (carried_in sched tsk arr) released_jobs = [::j_0] >>) \/
      filter (carried_in sched tsk arr) released_jobs = nil.
Proof.
Admitted.
  
Lemma workload_bound :
  forall ts sched (ARRts: ts_arrival_sequence ts sched)
         hp cpumap num_cpus (MULT: ident_mp num_cpus hp cpumap sched) 
         (RESTR: restricted_deadline_model ts)
         tsk (IN: tsk \in ts) j (JOB: job_task j = tsk)
         arr (ARRj: arrives_at sched j arr)
         (SCHED: task_misses_no_deadlines sched ts tsk),
    (workload sched ts tsk arr (arr + job_deadline j)) <= W tsk (arr + job_deadline j).
Proof.
  unfold workload; ins.
  generalize SCHED; apply carried_in_unique with (j := j) (arr := arr) in SCHED; des; ins;
  remember (prev_arrivals sched (arr + job_deadline j)) as released_jobs.
  (* Case 1: j_0 is the carried-in job *)
    assert (INj_0: j_0 \in released_jobs).
    {
      unfold carried_in in CARRY; unfold arrived, pending in *; des; subst.
      (*move: EARLIER => /exists_inP_nat EARLIER; des.
      rewrite (ts_finite_arrival_sequence ts) //.
      unfold arrived_before.
      apply/exists_inP_nat.
      exists x; split; [| by ins].
      apply ltn_trans with (n := arr).
      have a := (ltn_predK).*)
      admit.
    }

    rewrite (bigID (carried_in sched tsk arr)); simpl.
    apply leq_add.
    {
      rewrite -> eq_bigl with (P2 := fun j => carried_in sched tsk arr j);
      last (
          by unfold ssrfun.eqfun, carried_in, job_of; ins;
          rewrite andb_idl //; move/and3P => CARRYjob; destruct CARRYjob
      ).
      rewrite -big_filter FILTER big_cons big_nil addn0.
      rewrite leq_min; apply/andP; split.
      {
        move: CARRY => /and3P CARRY; destruct CARRY as [JOBj0 _ _].
        move: JOBj0 => /eqP JOBj0; rewrite -JOBj0.
        have PROP := job_properties j_0; des.
        apply leq_trans with (n := job_cost j_0); [|by ins].
        by apply service_interval_max_cost; [by unfold ident_mp in *; des].
      }
      {
        (* Prove that service of j_0 <= delta + d_k - e_k - n_k*p_k *)
        admit.
      }
    }
    {
      rewrite big_seq_cond.
        (* Prove that service of other jobs <= task_cost *)      
        apply leq_trans with
          (n := \sum_(i <- released_jobs | (i \in released_jobs) &&
                 job_of tsk i && ~~beq_job j_0 i) task_cost tsk).
        {
          apply leq_sum; unfold job_of; intros j_i. move/and3P.
          move/and3P => INj_i; des.
          move: INj_i INj_i0 => /andP INj_i NEQ; des.
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

          (* Prove that the number of non-carry-in jobs is at most n_k *)
          admit.
        }
      }
    }
    {
      (* There exists no carried-in job *)
      admit.
    }
Qed.

End WorkloadBound.