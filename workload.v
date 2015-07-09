Require Import Arith List Vbase job task schedule identmp priority helper task_arrival schedulability.

Section WorkloadBound.

(* The workload is defined as the total service received by jobs of
   a specific task in the interval [t,t'+1). To allow summing over the
   jobs released in the interval we assume that a list of arrived jobs
   (along with a proof that this is the right list) is passed by
   parameter. *)
Definition workload (sched: schedule) (ts: taskset) (tsk: sporadic_task) (t t': time)
                    (l: list job) (ARRlist: arrival_list sched l t') : nat :=
  fold_left plus (map
                    (fun j => service sched j t' - service sched j t) (* Check if off by 1*)
                    (filter (fun j => beq_nat (job_deadline j) 1) (* FIX: job_task j = tsk *)
                  l)
                 ) 0.

Definition W (tsk: sporadic_task) (delta: time) := 100. (* FIX: replace by formula later *)

Lemma workload_bound :
  forall ts sched (ARRts: ts_arrival_sequence ts sched)
         (RESTR: restricted_deadline_model ts)
         tsk (IN: In tsk ts) j (JOB: job_task j = tsk)
         arr (ARRj: arrives_at sched j arr)
         l (ARRlist: arrival_list sched l (arr + job_deadline j))
         (SCHED: task_misses_no_deadlines sched ts tsk),
    (workload sched ts tsk arr (arr + job_deadline j) l ARRlist) <= W tsk (job_deadline j).
Proof.
  ins.
  unfold workload. unfold task_misses_no_deadlines in *; des.
Admitted.

End WorkloadBound.