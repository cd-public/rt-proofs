Require Import Arith List Vbase job task schedule task_arrival
               schedulability divround sum.

Section WorkloadBound.

(* The workload is defined as the total service received by jobs of
   a specific task in the interval [t,t'). To allow summing over the
   jobs released in the interval we assume that a list of all jobs
   released before t' is passed by parameter. *)
Definition workload (sched: schedule) (ts: taskset) (tsk: sporadic_task) (t t': time)
                    (released_jobs: list job) : nat :=
  list_sum (map
             (fun j => service sched j t' - service sched j t)
             (filter (fun j => beq_task (job_task j) tsk) released_jobs)
           ).

Definition max_jobs (tsk: sporadic_task) (delta: time) :=
  div_floor (delta + task_deadline tsk - task_cost tsk) (task_period tsk).

Definition W (tsk: sporadic_task) (delta: time) :=
  let n_k := (max_jobs tsk delta) in
  let e_k := (task_cost tsk) in
  let d_k := (task_deadline tsk) in
  let p_k := (task_period tsk) in            
    n_k * e_k + min e_k (delta + d_k - e_k - n_k * p_k).

Lemma workload_bound :
  forall ts sched (ARRts: ts_arrival_sequence ts sched)
         (RESTR: restricted_deadline_model ts)
         tsk (IN: In tsk ts) j (JOB: job_task j = tsk)
         arr (ARRj: arrives_at sched j arr)
         released_jobs (ARRlist: arrival_list sched released_jobs (arr + job_deadline j))
         (SCHED: task_misses_no_deadlines sched ts tsk),
    (workload sched ts tsk arr (arr + job_deadline j) released_jobs) <= W tsk (job_deadline j).
Proof.
  ins.
  unfold workload. unfold task_misses_no_deadlines in *; des.
Admitted.

End WorkloadBound.