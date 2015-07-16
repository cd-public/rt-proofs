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
    min e_k (delta + d_k - e_k - n_k * p_k) + n_k * e_k.

Definition carried_in (sched: schedule) (tsk: sporadic_task) (t: time) (j: job) :=
  << TSKj: job_task j = tsk >> /\
  << EARLIER: arrived sched j (t - 1) >> /\
  << INTERF: exists t', t' >= t /\ pending sched j t' >>.


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
  remember (prev_arrivals sched (arr + job_deadline j)) as released_jobs.

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
      unfold carried_in in H; unfold arrived, pending in *; des; subst.
      move: EARLIER => /exists_inP_nat EARLIER; des.
      rewrite (ts_finite_arrival_sequence ts) //.
      unfold arrived_before.
      apply/exists_inP_nat.
      exists x; split; [| by ins].
      apply ltn_trans with (n := arr).
      have a := (ltn_predK).
      admit. admit.
    }

    rewrite big_seq_cond.
    rewrite (bigID (beq_job j_0)); simpl.
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
          apply leq_sum; unfold job_of; intros j_i.
          move/andP => INj_i; des.
          move: INj_i INj_i0 => /andP INj_i NEQ; des.
          unfold beq_task in *; destruct task_eq_dec as [JOBi|]; ins.
          apply leq_trans with
            (n := service sched j_i (arr + job_deadline j)).
          {
            (* service [arr, arr + d_k] <= service [0, arr + d_k] *)
            unfold service, service_during.
            have LE : arr <= arr + job_deadline j.
              by rewrite -{1}[arr]addn0; apply leq_add; ins.
            rewrite -> big_cat_nat with (m := 0) (n := arr); ins.
            rewrite -{1 1}[\sum_(arr <= t < arr + job_deadline j)
                  service_at sched j_i t] add0n.
            by apply leq_add; by ins.
          }
          {
            (* service <= task_cost *)
            have PROP := job_properties j_i; des.
            apply leq_trans with (n := job_cost j_i); [| by rewrite -JOBi].
            apply service_max_cost.
            by unfold ident_mp in MULT; des; by ins.
          }
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