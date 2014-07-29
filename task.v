Require Import Coq.Lists.List.
Import ListNotations.
Require Omega.

(* Sporadic Task Model (assumes integer time) *)
Record task : Type :=
  { cost: nat;
    period: nat;
    deadline: nat
  }.

(* Restrictions on the task parameters *)
Record well_defined_task (t: task) : Prop :=
  { cost_positive: cost t > 0;
    cost_le_period: cost t <= period t;
    cost_le_deadline: cost t <= deadline t;
    period_positive: period t > 0;
    deadline_positive: deadline t > 0
  }.

(* Unit tests for task*)
Section Test_task.
Example bad_task_parameters1 : ~ well_defined_task {| cost := 4; period := 42; deadline := 0 |}.
Proof.
  intro H. apply deadline_positive in H. simpl in H. inversion H. Qed.

Example bad_task_parameters2 : ~ well_defined_task {| cost := 4; period := 2; deadline := 2 |}.
Proof.
  intro H. apply cost_le_period in H. simpl in H. omega. Qed.

Example good_task_parameters1 : well_defined_task {| cost := 4; period := 42; deadline :=  45|}.
Proof.
  constructor; simpl; omega. Qed.
End Test_task.

(* Deadline restriction *)
Definition deadline_implicit (t: task) : Prop := deadline t = period t.
Definition deadline_restricted (t: task) : Prop := deadline t <= period t.
Definition deadline_arbitrary (t: task) : Prop := True.

Theorem implicit_is_restricted : forall (t: task), deadline_implicit t -> deadline_restricted t.
Proof.
  unfold deadline_implicit. unfold deadline_restricted.
  intros t H. rewrite H. apply le_n. Qed. 

Theorem restricted_is_arbitrary : forall (t: task), deadline_restricted t -> deadline_arbitrary t.
Proof.
  unfold deadline_arbitrary. intros t H. apply I. Qed.

(* Testing task extension (slices) *)
Definition task_cost_sum (l: list task) : nat := fold_left plus (map cost l) 0.

Record sliced_task : Type :=
  { s_task :> task; (* allows this type to be applied implicitly as a task *)
    slices : list task
  }.

Record well_defined_sliced_task (t: sliced_task) : Prop :=
  { _ :> well_defined_task t;
    accumulated_cost: task_cost_sum (slices t) = cost t
  }.

Section Test_sliced.
Example good_sliced_task1 :
      well_defined_sliced_task
        {| s_task := {| cost := 6; period := 42; deadline := 12 |};
           slices := [{| cost := 4; period := 42; deadline := 12|};
                          {| cost := 2; period := 42; deadline := 12|}] |}.
Proof.
  repeat constructor. Qed.

Example bad_sliced_task1 :
      ~well_defined_sliced_task
        {| s_task := {| cost := 6; period := 42; deadline := 12 |};
           slices := [{| cost := 5; period := 42; deadline := 12|};
                          {| cost := 2; period := 42; deadline := 12|}] |}.
Proof.
  intro H. inversion H. inversion H0.
  compute in accumulated_cost0. inversion accumulated_cost0. Qed.
End Test_sliced.

(*Inductive processor (n: nat) : Type :=
  | cpu : processor n. *)

Definition proc := nat.

Definition sched := nat * proc  -> option task.

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