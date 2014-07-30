Require Import Coq.Lists.List.
Require Import Sets.
Require Import Maps.
Require Import Coq.Arith.EqNat.

Set Printing Projections.

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

(*Definition next_job (j: job) : job :=
  exists j': job,
  {| id := id j;
     number := number j + 1;
     arrival := arrival j + ;
     cost := cost j;
     deadline := deadline j
  |}.*)

Definition taskset := list sporadic_task.

Definition valid_taskset (ts: taskset) : Prop := True. (* TODO fix *)

Definition processor := nat.
Definition time := nat.

Record schedule_state : Type :=
  {
    instant: time;
    cpu_count: nat;
    task_map: Map [processor, job];
    active_jobs : list job
  }.

Record valid_schedule_state (s: schedule_state) : Prop :=
  {
  number_cpus:
    forall cpu job, MapsTo cpu job (task_map s) -> cpu < cpu_count s;

  mutual_exclusion:
    forall cpu1 cpu2 job, MapsTo cpu1 job (task_map s) ->
                          MapsTo cpu2 job (task_map s) ->
                          cpu1 = cpu2;
  task_map_is_valid:
    forall cpu job, MapsTo cpu job (task_map s) -> List.In job (active_jobs s)
  }.

Definition sched_algorithm := schedule_state -> schedule_state.

Definition event := prod time (schedule_state -> schedule_state).

Definition compute_event (s: schedule_state) (ev: event) : schedule_state :=
  match beq_nat (instant s) (fst ev) with
  | true => (snd ev) s
  | false => s
  end.

Definition process_events (s: schedule_state) (events: list event) : schedule_state :=
  fold_left compute_event events s.

Print beq_nat.
Definition clear_events (s: schedule_state) (events: list event) : list event :=
  List.filter (fun ev => negb (beq_nat (instant s) (fst ev))) events.
(*TODO add examples to check correctness *)

Definition ev_job_arrival (j: job) (state: schedule_state) : schedule_state :=
  {|
    instant := instant state;
    cpu_count := cpu_count state;
    task_map := task_map state;
    active_jobs := cons j (active_jobs state)
  |}.

(* ev_task_init converts a list of sporadic_task into a list of initial events in the form:
   <(task0_offset, task0_job0), (task1_offset, task1_job0), (task2_offset, task2_job0), ...>*)
Definition ev_taskset_init (ts: taskset) : list event :=
  List.map (fun (x: sporadic_task) => pair (st_offset x) (ev_job_arrival (first_job x))) ts.

Print empty.

Definition empty_schedule (num_cpus: nat) : schedule_state :=
  {|
    instant := 0;
    cpu_count := num_cpus;
    task_map := [];
    active_jobs := nil
  |}.

Inductive schedule (num_cpus: nat) (alg: sched_algorithm) :
                taskset -> schedule_state -> list event -> Type :=
  (* sched_init(alg, ts) gives the initial state *)
  | sched_init :
      forall (ts: taskset) (state: schedule_state),
        let state0 := (empty_schedule 1) in
        let events0 := (ev_taskset_init ts) in
        let state' := (process_events state0 events0) in
        let events' := (clear_events state0 events0) in
               valid_taskset ts -> schedule num_cpus alg ts state' events'
  (* sched_next(alg, ts, state) moves to the next state *)
  | sched_next :
      forall (ts: taskset) (state: schedule_state) (events: list event),
        let state' := (process_events state events) in
        let events' := (clear_events state events) in
          schedule num_cpus alg ts state events
            -> schedule num_cpus alg ts state' events'.

(*Inductive schedule (alg: sched_algorithm) : taskset -> schedule_state -> list event -> Type :=
  (* sched_init(alg, ts) gives the initial state *)
  | sched_init : forall (ts: taskset) (state: schedule_state),
                           valid_taskset ts -> schedule alg ts state nil
  (* sched_next(alg, ts, state) moves to the next state *)
  | sched_next : forall (ts: taskset) (state: schedule_state) (events: list event),
                           schedule alg ts state events
                           -> schedule alg ts (alg (process_events state events)) (clear_events state events).*)

Theorem schedule_always_valid :
  forall (num_cpus: nat) (alg: sched_algorithm) (ts: taskset) (state: schedule_state) (events: list event),
           schedule num_cpus alg ts state events -> valid_schedule_state state.
  Proof.
    intros num_cpus alg ts state events H.
    induction H.
    constructor. 

Definition cpu_idle (cpu: processor) (s: schedule_state) : Prop :=
  forall j, ~MapsTo cpu j (task_map s).

Definition job_backlogged (j: job) (s: schedule_state) : Prop :=
  List.In j (active_jobs s) /\ forall cpu, ~MapsTo cpu j (task_map s).

Definition break_ties (j1 j2: job) : Prop :=
  job_id j1 < job_id j2 \/ job_number j1 < job_number j2.

Definition prio_order := job -> job -> Prop. (* job_a < job_b *)

Definition prio_EDF (j1 j2: job) : Prop :=
  job_deadline j1 < job_deadline j2 \/ break_ties j1 j2.

Definition enforce_priority (higher_prio: prio_order) (s: schedule_state) : Prop :=
  forall cpu, cpu_idle cpu s
              \/ exists j, MapsTo cpu j (task_map s)
                           -> (forall b, job_backlogged b s -> higher_prio j b). 

(* TODO add unique priorities *)
(* TODO add some predicates to indicate CPU allowance -> add affinities in the future *)

Definition work_conserving (s: schedule_state) : Prop :=
  forall cpu, cpu_idle cpu s -> forall j, ~job_backlogged j s.

Definition sched_EDF (s: schedule_state) : Prop :=
  work_conserving s /\ enforce_priority prio_EDF s.

Definition EDF (s: schedule_state) : schedule_state :=
  let 

  {| cpu_count := cpu_count s;
     task_map := ;
     active_jobs := active_jobs s;
  |}.

Print (sched_init ts).

  | sched_next : forall (state: schedule_state), schedule state -> schedule state.

Inductive schedule : taskset -> Type :=
  | sched_init : forall (ts: taskset), schedule ts.

Inductive schedule : schedule_state -> Type :=
  | sched_init : forall (ts: taskset), valid_taskset ts -> schedule ts
  | sched_next : forall (state: schedule_state), schedule state -> schedule state.


Definition start (ts: taskset) : schedule_state :=
    Build_schedule_state{| mapping := (fun (x: nat) (p: proc) => None); ready_queue:= nil |}.

Inductive schedule : taskset -> Type :=
  | sched_init : forall (ts: taskset), schedule ts
  | sched_init_at : forall (ts: taskset), schedule ts
  | sched_next : forall (state: schedule_state), schedule ts -> schedule ts.



Section Schedule.
  Variable mapping : nat * proc  -> option job.
End Schedule.

Inductive schedule : taskset -> Prop :=
  | sched_init : forall (ts: taskset), schedule ts
  | sched_next : forall (ts: taskset), schedule ts -> schedule ts.


Inductive all (X : Type) (P : X -> Prop) : list X -> Prop :=
  | all_nil : all X P nil
  | all_cons :  forall (l : list X) (h : X), (all X P l) ->  P h -> all X P (h::l).

Record schedule : Type :=
  { instant: nat;
    mapping: nat; (*task to processor mapping*)
    cost_le_deadline: cost j <= deadline j;
    deadline_positive: deadline j > 0
  }.

Theorem good_schedule : forall s: sched, j:job

Definition proc := nat.

Definition sched := nat * proc  -> option job.

(*Inductive nat_interval : nat -> nat ->Type :=
  | interval_O : forall (a: nat), nat_interval a a
  | interval_S : forall (a b: nat), nat_interval a b -> nat_interval a (S b).*)

Record interval : Type :=
  { start: nat;
    len: nat
  }.

Definition executes (t: task) (s: sched) (time: nat) := 

Fixpoint total_exec (t: task) (s: sched) (i: interval) :=
  match len i with
    O => O.
    S n' => match s with
                  
                 end
  end.

Section Test_sched.
Definition 
Example test1 : exists s:sched, s (2, 3) = Some {| cost := 6; period := 42; deadline :=1|}.
Proof.
  auto. trivial.
End Test_sched.