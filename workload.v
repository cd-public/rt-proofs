Require Import Classical List Arith Vbase job task schedule task_arrival
        schedulability divround sum
        ssrbool eqtype ssrnat seq div fintype bigop ssromega.

Section WorkloadBound.
  
Definition job_of (tsk: sporadic_task) (j: job) : bool :=
  beq_task (job_task j) tsk.

(* The workload is defined as the total service received by jobs of
   a specific task in the interval [t,t'). To allow summing over the
   jobs released in the interval we assume that a list of all jobs
   released before t' is passed by parameter. *)
Definition workload (sched: schedule) (ts: taskset) (tsk: sporadic_task) (t t': time) :=
  let released_jobs := arrival_list sched t' in
    \sum_(j <- released_jobs | job_of tsk j) (service_during sched j t t').

Definition max_jobs (tsk: sporadic_task) (delta: time) :=
  div_floor (delta + task_deadline tsk - task_cost tsk) (task_period tsk).

Definition W (tsk: sporadic_task) (delta: time) :=
  let n_k := (max_jobs tsk delta) in
  let e_k := (task_cost tsk) in
  let d_k := (task_deadline tsk) in
  let p_k := (task_period tsk) in            
    min e_k (delta + d_k - e_k - n_k * p_k) + n_k * e_k.

Definition carried_in (sched: schedule) (tsk: sporadic_task) (t: time) (j: job) :=
  << TSKj: job_task j == tsk >> /\
  << EARLIER: arrived sched j (t - 1) >> /\
  << INTERF: exists t', t' >= t /\ pending sched j t' >>.

Lemma workload_bound :
  forall ts sched (ARRts: ts_arrival_sequence ts sched)
         (RESTR: restricted_deadline_model ts)
         tsk (IN: tsk \in ts) j (JOB: job_task j = tsk)
         arr (ARRj: arrives_at sched j arr)
         (SCHED: task_misses_no_deadlines sched ts tsk),
    (workload sched ts tsk arr (arr + job_deadline j)) <= W tsk (arr + job_deadline j).
Proof.
  unfold workload; ins.
  remember (arrival_list sched (arr + job_deadline j)) as released_jobs.

  (* There exists at most one carried-in job *)
  assert (UNIQcarry:
            forall j1 j2 (IN1: j1 \in released_jobs)
                   (IN2: j2 \in released_jobs)
                   (C1: carried_in sched tsk arr j1)
                   (C2: carried_in sched tsk arr j2), j1 = j2).
  {
    ins. admit.
  }

  destruct (classic (exists j_0, carried_in sched tsk arr j_0)); des.
  {
    (* Carried-in job j_0 *)
    assert (INj_0: j_0 \in released_jobs).
    {
      unfold carried_in in H. unfold arrived in *; des.
      subst.
      rewrite -> ts_finite_arrival_sequence with (ts := ts); ins.
      admit.
      unfold released_jobs.
      ,  arrived in *. rewrite ARRlist; des.
      by exists t_0; split; [ssromega|].
      -------------------------------BROKEN because \in <> In*)
      admit.
    }

    rewrite big_seq_cond.
    rewrite (bigID (beq_job j_0)); simpl.
    unfold W.
    apply leq_add.
    {
      (* Prove that the service of the carried-in job <= min()*)
      admit.
      }
      {
        (* Prove that service of other jobs <= task_cost *)      
        apply leq_trans with
          (n := \sum_(i <- released_jobs | (i \in released_jobs) &&
                 job_of tsk i && ~~beq_job j_0 i) task_cost tsk).
        {
          apply leq_sum; intro j_i; ins.
          unfold service_during, andb, negb in *; desf.
          rewrite leq_subLR.
          rewrite <- addn0; rewrite addnC.
          rewrite leq_add; ins.
          (*easy to prove, since j_i does not execute for more than WCET *)
          admit.
        }
        {
          rewrite big_const_seq, iter_addn, addn0, mulnC.
          rewrite leq_mul2r.
          unfold orb; desf.
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