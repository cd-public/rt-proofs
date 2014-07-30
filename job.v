Require Import Coq.Lists.List.
Require Import Sets.
Require Import Maps.

Set Printing Projections.

(* A job represents an execution requirement *)
Inductive job : Type :=
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
    cpu_count: nat;
    task_map: Map [processor, job];
    ready_queue : list job
  }.

Record valid_schedule_state (s: schedule_state) : Prop :=
  {
  number_cpus:
    forall cpu job, MapsTo cpu job (task_map s) -> cpu < cpu_count s;

  mutual_exclusion:
    forall cpu1 cpu2 job, MapsTo cpu1 job (task_map s) ->
                          MapsTo cpu2 job (task_map s) ->
                          cpu1 = cpu2;
  running_inter_idle_is_empty:
    forall cpu job, MapsTo cpu job (task_map s) /\ List.In job (ready_queue s) -> False
  }.

Definition sched_algorithm := schedule_state -> schedule_state.

(* Generic schedule type*)
Inductive schedule (alg: sched_algorithm) : taskset -> schedule_state -> Type :=
  | sched_init : forall (ts: taskset) (state: schedule_state),
                           valid_taskset ts -> schedule alg ts state
  | sched_next : forall (ts: taskset) (state: schedule_state),
                           schedule alg ts state -> (schedule alg ts (alg state)).

Definition EDF (s: schedule_state) : schedule_state :=
  {| cpu_count := cpu_count s;
     task_map :=;
     ready_queue :=;
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