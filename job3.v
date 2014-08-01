Require Import Coq.Lists.List.
Require Import Coq.Arith.EqNat.

(* A job represents an execution requirement *)
Record job : Type :=
  { job_id: nat; (* identifier *)
    job_number: nat; (* sequence number *)
    job_arrival: nat;
    job_cost: nat;
    job_deadline: nat
  }.

(* Restrictions on job parameters *)
Record well_defined_job (j: job) : Prop :=
  { job_cost_positive: job_cost j > 0;
    job_cost_le_deadline: job_cost j <= job_deadline j;
    job_deadline_positive: job_deadline j > 0
  }.

(* Sporadic Task Model (assumes integer time) *)
Record sporadic_task : Type :=
  { st_id: nat;
    st_cost: nat;
    st_period: nat;
    st_deadline: nat;
    st_offset: nat
  }.

(* Restrictions on the task parameters *)
Record well_defined_task (t: sporadic_task) : Prop :=
  { st_cost_positive: st_cost t > 0;
    st_cost_le_period: st_cost t <= st_period t;
    st_cost_le_deadline: st_cost t <= st_deadline t;
    st_period_positive: st_period t > 0;
    st_deadline_positive: st_deadline t > 0
  }.

Definition first_job (t: sporadic_task) : job :=
  {| job_id := st_id t;
     job_number := 0;
     job_arrival := st_offset t;
     job_cost := st_cost t;
     job_deadline := st_deadline t
  |}.

Definition taskset := list sporadic_task.

Definition valid_taskset (ts: taskset) : Prop := True. (* TODO fix *)

Definition processor := nat.
Definition time := nat.

Record schedule_state : Type :=
  {
    instant: time;
    cpu_count: nat;
    task_map: list (option job); (*task_map: Map [processor, job];*)
    active_jobs : list job
  }.

Definition scheduled (j: job) (cpu: processor) (s: schedule_state) : Prop :=
  nth cpu (task_map s) None = Some j.

Record valid_schedule_state (s: schedule_state) : Prop :=
  {
  number_cpus:
    length (task_map s) = cpu_count s;

  mutual_exclusion:
    forall j cpu1 cpu2, scheduled j cpu1 s ->
                        scheduled j cpu2 s ->
                        cpu1 = cpu2;
  task_map_is_valid:
    forall j cpu, scheduled j cpu s -> List.In j (active_jobs s)
  }.

Definition sched_algorithm := schedule_state -> schedule_state.

Fixpoint list_none (n:nat) : list (option job) :=
  match n with
  | O => nil
  | S n => None :: (list_none n)
  end.

Definition empty_schedule (num_cpus: nat) : schedule_state :=
  {|
    instant := 0;
    cpu_count := num_cpus;
    task_map := list_none num_cpus;
    active_jobs := nil
  |}.

Definition schedule := Type.

(* arrives_at (schedule, task, job_num, time): All possible arrival sequences for a job *)
Inductive arrives_at (s: schedule) (task: sporadic_task) : nat -> time -> Prop :=
  | arrives_at_offset: arrives_at s task 0 (st_offset task)
  | arrives_next: forall (num_job: nat) (t: time) (k: nat),
                                   arrives_at s task num_job t ->
                                   arrives_at s task (num_job + 1) (t + (st_period task) + k).

Definition active_at (s: schedule) (task: sporadic_task) (num_job: nat) (t: time) : Prop :=
  forall (t0: time), arrives_at s task num_job t0 /\ t0 <= t.

Parameter scheduled_at: schedule -> sporadic_task -> nat -> time -> Prop.

Axiom mutual_exclusion

Definition F

Section Schedule.
End Schedule.

Inductive cumulative_exec (s: schedule) (task: sporadic_task) (job_num: nat) : time -> nat -> Prop :=
  | released: forall (t: time),
         arrives_at s task job_num t ->
         cumulative_exec s task job_num t 0
  | pending: forall (t: time) (current_exec: time),
         current_exec < (st_cost task) ->
         active_at s task job_num t ->
         (*not (exists cpu, scheduled job cpu s) at time t ->*)
         cumulative_exec s task job_num (t+1) (current_exec)
  | executing: forall (t: time) (current_exec: time),
         current_exec < (st_cost task) ->
         active_at s task job_num t ->
         (*(exists cpu, scheduled job cpu s) at time t ->*)
         cumulative_exec s task job_num (t+1) (current_exec+1)
  | completed: forall (t: time) (current_exec: time),
         current_exec = (st_cost task) ->
         active_at s task job_num t ->
         (*(exists cpu, scheduled job cpu s) at time t ->*)
         cumulative_exec s task job_num (t+1) (current_exec).

Example test_exec1 : forall (s: schedule) (task: sporadic_task),
      st_cost task = 7 /\ cumulative_exec s task 13 5 7 -> cumulative_exec s task 13 6 7.
Proof.
  intros. assert (cumulative_exec s task 13 6 7 = cumulative_exec s task 13 (5+1) 7). auto. rewrite H0.
  apply completed. inversion H. symmetry. apply H1. inversion H. inversion H2. inversion H2. apply H5. simpl. apply completed.


Inductive cumulative_exec (s: schedule) (task: sporadic_task) (job_num: nat) : time -> nat -> Prop :=
  | exec_completed: forall (t: time) (k: time),
         arrives_at s task job_num t ->
         cumulative_exec s task job_num (t+k) (st_cost task) ->
         cumulative_exec s task job_num (t+k+1) (st_cost task)
  | pending: forall (t: time) (k: time),
         arrives_at s task job_num t ->
         cumulative_exec s task job_num (t) (st_cost task) ->
         cumulative_exec s task job_num (t+1) (st_cost task).
  | executing: forall (t: time) (k: time),
         arrives_at s task job_num t ->
         (exists cpu, scheduled job cpu s) -> 
         cumulative_exec s task job_num (t+1) (st_cost task) ->
         cumulative_exec s task job_num (t+1) (st_cost task).

arrives_atarrives_at s task 0 (st_offset task).


  | arrives_next: forall (num_job: nat) (t: time) (k: nat),
                                   arrives_at s task num_job t ->
                                   arrives_at s task (num_job + 1) (t + (st_period task) + k).

Inductive schedule (ts: taskset) : time -> Type :=
  | sched_init : schedule ts 0
  | sched_next:
                forall (t: time), schedule ts t  -> schedule ts (t+1).


                taskset -> schedule_state -> Prop :=


Inductive schedule (num_cpus: nat) (alg: sched_algorithm) :
                taskset -> schedule_state -> Prop :=
  (* sched_init(alg, ts) gives the initial state *)
  | sched_init :
      forall (ts: taskset) (state: schedule_state),
        let state0 := (empty_schedule num_cpus) in
        let state' := alg (process_events state0 events0) in
              valid_taskset ts ->
              preserves_validity alg ->
              schedule num_cpus alg ts state' events'
  (* sched_next(alg, ts, state) moves to the next state *)
  | sched_next :
      forall (ts: taskset) (state: schedule_state) (events: list event),
        let state' := alg (process_events state events) in
          preserves_validity alg ->
          schedule num_cpus alg ts state ->
          schedule num_cpus alg ts state'.

Inductive arrives_at (s: schedule) (task: sporadic_task) (job_num: nat) : nat -> Prop :=
  | arrives_at_offset: arrives_at s task 0 (st_offset task)
  | arrives_next: forall (num_job: nat) (t: time),
                                   arrives_at s task num_job t ->
                                   arrives_at s task (num_job + 1) (t + (st_period task)).

Inductive arrival_sequence (t: sporadic_task) : nat Prop :=

Inductive schedule (num_cpus: nat) (alg: sched_algorithm) :
                taskset -> schedule_state -> list event -> Prop :=
  (* sched_init(alg, ts) gives the initial state *)
  | sched_init :
      forall (ts: taskset) (state: schedule_state),
        let state0 := (empty_schedule num_cpus) in
        let events0 := (ev_taskset_init ts) in
        let state' := alg (process_events state0 events0) in
        let events' := (clear_events state0 events0) in
              (*num_cpus > 0 ->*)
              valid_taskset ts ->
              preserves_validity alg ->
              schedule num_cpus alg ts state' events'
  (* sched_next(alg, ts, state) moves to the next state *)
  | sched_next :
      forall (ts: taskset) (state: schedule_state) (events: list event),
        let state' := alg (process_events state events) in
        let events' := (clear_events state events) in
          good_event_list events ->
          preserves_validity alg ->
          schedule num_cpus alg ts state events ->
          schedule num_cpus alg ts state' events'.

Definition cpu_idle (cpu: processor) (s: schedule_state) : Prop :=
  forall j, ~scheduled j cpu s.

Definition job_backlogged (j: job) (s: schedule_state) : Prop :=
  List.In j (active_jobs s) /\ forall cpu, ~scheduled j cpu s.

Definition break_ties (j1 j2: job) : Prop :=
  job_id j1 < job_id j2 \/ job_number j1 < job_number j2.

Definition prio_order := job -> job -> Prop. (* job_a < job_b *)

Definition prio_EDF (j1 j2: job) : Prop :=
  job_deadline j1 < job_deadline j2 \/ break_ties j1 j2.

Definition enforce_priority (higher_prio: prio_order) (s: schedule_state) : Prop := forall cpu,
  cpu_idle cpu s
  \/ (exists j, scheduled j cpu s -> (forall b, job_backlogged b s -> higher_prio j b)). 

(* TODO add unique priorities *)
(* TODO add some predicates to indicate CPU allowance -> add affinities in the future *)

Definition work_conserving (s: schedule_state) : Prop :=
  forall cpu, cpu_idle cpu s -> forall j, ~job_backlogged j s.

Definition sched_EDF (s: schedule_state) : Prop :=
  work_conserving s /\ enforce_priority prio_EDF s.