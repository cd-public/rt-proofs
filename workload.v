Require Import Classical Arith List Vbase job task schedule task_arrival
               schedulability divround sum.

Section WorkloadBound.

Definition job_of (tsk: sporadic_task) (j: job) : bool :=
  beq_task (job_task j) tsk.
  
(* The workload is defined as the total service received by jobs of
   a specific task in the interval [t,t'). To allow summing over the
   jobs released in the interval we assume that a list of all jobs
   released before t' is passed by parameter. *)
  Definition workload (sched: schedule) (ts: taskset) (tsk: sporadic_task)
                      (t t': time) (released_jobs: list job) : nat :=
  list_sum (map
             (fun j => service sched j t' - service sched j t)
             (filter (job_of tsk) released_jobs)
           ).

Definition max_jobs (tsk: sporadic_task) (delta: time) :=
  div_floor (delta + task_deadline tsk - task_cost tsk) (task_period tsk).

Definition W (tsk: sporadic_task) (delta: time) :=
  let n_k := (max_jobs tsk delta) in
  let e_k := (task_cost tsk) in
  let d_k := (task_deadline tsk) in
  let p_k := (task_period tsk) in            
    n_k * e_k + min e_k (delta + d_k - e_k - n_k * p_k).

Definition carried_in (sched: schedule) (j: job)
                      (tsk: sporadic_task) (start: time) :=
  << TSKj: job_task j = tsk >> /\
  << EARLIER: arrived sched j (start - 1) >> /\
  exists t', << LATER: t' >= start >> /\
             << SCHED: scheduled sched j t' >>.

Lemma workload_bound :
  forall ts sched (ARRts: ts_arrival_sequence ts sched)
         (RESTR: restricted_deadline_model ts)
         tsk (IN: In tsk ts) j (JOB: job_task j = tsk)
         arr (ARRj: arrives_at sched j arr)
         released_jobs (ARRlist: arrival_list sched released_jobs (arr + job_deadline j - 1))
         (SCHED: task_misses_no_deadlines sched ts tsk),
    (workload sched ts tsk arr (arr + job_deadline j) released_jobs) <= W tsk (job_deadline j).
Proof.
  ins.
  unfold workload.
  destruct (classic (arr = 0)) as [| NZEROarr]; try subst arr.
    (* j arrives at time 0: no carried-in job *)
    admit.
    (* j arrives at later time *)
    destruct (classic (exists j_0, carried_in sched j_0 tsk arr)); des.
    {
      (* Carried-in job j_0 *)
      assert (INj_0: In j_0 released_jobs).
      {
        unfold carried_in, arrival_list, arrived in *; rewrite ARRlist; des.
        by exists t_0; split; [omega|].
      }
      (* Only one carried-in job *)
      assert (UNIQcarry:
                forall j1 j2 (C1: carried_in sched j1 tsk arr)
                       (C2: carried_in sched j2 tsk arr), j1 = j2).
      {
        ins. admit.
      }
      remember (partition (fun j => beq_nat (job_deadline j) 0)
                          (filter (job_of tsk) released_jobs)) as part_carry.
      destruct part_carry as [l_carry l_rest].
      rewrite sum_list_partition with (l1 := l_carry) (l2 := l_rest) (f := fun j => beq_nat (job_deadline j) 0).
      admit.
    }
    {
      (* No carried-in job *)
      admit.
    }
Qed.

End WorkloadBound.