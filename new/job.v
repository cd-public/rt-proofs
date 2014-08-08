Require Import Coq.Lists.List.
Require Import Coq.Arith.EqNat.

(* Sporadic Task Model (assumes integer time) *)
Record sporadic_task : Type :=
  { st_id: nat;
    st_cost: nat;
    st_period: nat;
    st_deadline: nat;
    st_offset: nat;
    st_arrival: nat -> nat
  }.

(* Restrictions on the task parameters *)
Record well_defined_task (task: sporadic_task) : Prop :=
  { st_cost_positive: st_cost task > 0;
    st_cost_le_period: st_cost task <= st_period task;
    st_cost_le_deadline: st_cost task <= st_deadline task;
    st_period_positive: st_period task > 0;
    st_deadline_positive: st_deadline task > 0;
    st_arrival_start: st_arrival task 0 = st_offset task;
    st_arrival_valid: forall i, st_arrival task i <= st_arrival task (i+1) + st_period task
  }.

Definition taskset := list sporadic_task.

(* A job represents an execution requirement *)
Record job : Type :=
  { job_id: sporadic_task; (* identifier *)   (*TODO Fix -- Make this more generic*)
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