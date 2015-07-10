Require Import Arith List Vbase job task schedule identmp priority helper task_arrival schedulability.

Section WorkloadBound.

(* The workload is defined as the total service received by jobs of
   a specific task in the interval [t,t'+1). To allow summing over the
   jobs released in the interval we assume that a list of arrived jobs
   is passed by parameter. *)
Definition workload (sched: schedule) (ts: taskset) (tsk: sporadic_task) (t t': time)
                    (released_jobs: list job) : nat :=
  fold_left plus (map
                    (fun j => service sched j (t'-1) - service sched j t)
                    (filter (fun j => beq_task (job_task j) tsk)
                  released_jobs)
                 ) 0.

Definition W (tsk: sporadic_task) (delta: time) := 100. (* FIX: replace by formula later *)

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