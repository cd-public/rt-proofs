Add LoadPath "/home/felipec/dev/coq/rt-scheduling-spec".
Require Import job.
Require Import Coq.Lists.ListSet.

Definition time := nat.

Axiom schedule : Set.
Axiom scheduled : task -> schedule -> nat -> Prop.
Axiom exec : task -> schedule -> nat -> nat.

Definition cpu_platform := Set.
Axiom cpuset : schedule -> cpu_platform.

Record ident_mp (platform: cpu_platform) (num_cpus: nat) : Prop :=
  { maximum_cpus: forall (s: schedule) (t: time),
           cpuset s = platform ->
               (exists (l: list task),
                   length l < num_cpus /\
                   forall (tsk: task),
                       List.In tsk l <-> scheduled tsk s t)
  }.

Axiom 

Fixpoint service (tsk: task) (s: schedule) (t: time) : nat:=
  match t with
  | 0=> 0
  | Sn=> 1
  end.