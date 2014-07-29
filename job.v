Require Import Coq.Lists.List.
Require Import Sets.
Require Import Maps.

(* A job represents an execution requirement *)
Record job : Type :=
  { arrival: nat;
    cost: nat;
    deadline: nat
  }.

(* Restrictions on job parameters *)
Record well_defined_job (j: job) : Prop :=
  { cost_positive: cost j > 0;
    cost_le_deadline: cost j <= deadline j;
    deadline_positive: deadline j > 0
  }.

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