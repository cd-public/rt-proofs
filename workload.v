Require Import Classical Arith List Vbase job task schedule task_arrival
               schedulability divround sum ssreflect ssrbool ssrnat bigop.

Section WorkloadBound.

Definition job_of (tsk: sporadic_task) (j: job) : bool :=
  beq_task (job_task j) tsk.
  
(* The workload is defined as the total service received by jobs of
   a specific task in the interval [t,t'). To allow summing over the
   jobs released in the interval we assume that a list of all jobs
   released before t' is passed by parameter. *)
Definition workload (sched: schedule) (ts: taskset) (tsk: sporadic_task)
                     (t t': time) (released_jobs: list job) : nat :=
  \sum_(j <- released_jobs | job_of tsk j) (service sched j t' - service sched j t).

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
  exists t', << LATER: t' >= t >> /\
             << SCHED: scheduled sched j t' >>.

Definition carried_in_dec (sched: schedule) (tsk: sporadic_task) (t: time) (j: job) := job_of tsk j.
(* I need a decidable version of carried_in!!! *)

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
    destruct (classic (exists j_0, carried_in sched tsk arr j_0)); des.
    {
      (* Carried-in job j_0 *)
      (*assert (INj_0: In j_0 released_jobs).
      {
        unfold carried_in, arrival_list, arrived in *; rewrite ARRlist; des.
        by exists t_0; split; [omega|].
      }
      (* Only one carried-in job *)
      assert (UNIQcarry:
                forall j1 j2 (C1: carried_in sched tsk arr j1)
                       (C2: carried_in sched tsk arr j2), j1 = j2).
      {
        ins. admit.
      }*)

      rewrite (bigID (carried_in_dec sched tsk arr)) /=.
      apply leq_add.
        (* Prove that cost of all carried in-jobs <= min() *)
        admit.
        (* Prove that cost of all normal jobs <= e_k * n_k *)
        admit.
    }
    {
      (* No carried-in job *)
      admit.
    }
Qed.

End WorkloadBound.