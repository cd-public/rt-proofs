Require Import Vbase task task_arrival job schedule helper platform priority
               ssrbool ssrnat seq bigop. 

Definition response_time_ub_sched (sched: schedule) (ts: taskset) (tsk: sporadic_task) (R: time) :=
  << IN: tsk \in ts >> /\
  << ARRts: ts_arrival_sequence ts sched >> /\
  forall j (JOBj: job_of tsk j) t_a (ARRj: arrives_at sched j t_a),
    completed sched j (t_a + R).

Definition response_time_ub (platform: processor_platform) (ts: taskset) (tsk: sporadic_task) (R: time) :=
  << IN: tsk \in ts >> /\
  forall sched (PLAT: platform sched)
         (ARRts: ts_arrival_sequence ts sched)
         j (JOBj: job_of tsk j) t_a (ARRj: arrives_at sched j t_a),
    completed sched j (t_a + R).

Lemma service_after_rt :
  forall plat (sched: schedule) ts tsk j (JOBj: job_of tsk j)
         R_tsk (RESP: response_time_ub plat ts tsk R_tsk)
         t' (GE: t' >= job_arrival j + R_tsk),
    service_at sched j t' = 0.
Proof.
Admitted.

Lemma sum_service_after_rt :
  forall plat (sched: schedule) ts tsk j (JOBj: job_of tsk j)
         R_tsk (RESP: response_time_ub plat ts tsk R_tsk)
         t0 t' (GE: t0 >= job_arrival j + R_tsk),
    \sum_(t0 <= t < t') service_at sched j t = 0.
Proof.
Admitted.

(*Section ResponseTime.

(* Response time bounds are platform-specific.*)
Variable platform: cpu_platform.
Variable hp: higher_priority.

(* Response time of a job in a particular schedule *)
Definition job_response_time (sched: schedule) (j: job) (r: time) : Prop :=
  forall t_a (ARRj: arrives_at sched j t_a),
    least_nat r (fun r => completed sched j (t_a + r)).

Definition total_interference (sched: schedule) (j: job) (t: time) : Prop :=
    job_response_time sched j (t + job_cost j).

(* Worst-case response time of any job of a task, in any schedule *)
Definition task_response_time_ub (tsk: sporadic_task) (ts: taskset) (R: time) : Prop :=
  forall (IN: In tsk ts) (sched: schedule) j t_a r
         (PLAT: platform sched) (ARRts: ts_arrival_sequence ts sched)
         (JOBj: job_of j = Some tsk) (ARRj: arrives_at sched j t_a)
         (RTj: job_response_time sched j r), r <= R.

Definition task_response_time_max (tsk: sporadic_task) (ts: taskset) (r: time) :=
  << RTub: task_response_time_ub tsk ts r >> /\
  exists (sched: schedule) (j: job),
    << PLAT: platform sched >> /\
    << ARRts: ts_arrival_sequence ts sched >> /\
    << JOBj: job_of j = Some tsk >> /\
    << RTj: job_response_time sched j r >>.

(* Critical instant is an arrival time in some schedule that generates the worst-case response time.
   Every arrival time whose response time is unbounded is also critical. *)
Definition critical_instant (tsk: sporadic_task) (ts: taskset) (sched: schedule) (t: time) :=
  exists j,
    << JOBj: job_of j = Some tsk >> /\
    << ARRj: arrives_at sched j t >> /\
    forall r (RTj: job_response_time sched j r), task_response_time_ub tsk ts r.

End ResponseTime.
*)