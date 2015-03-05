Add LoadPath "/home/felipec/dev/coq/rt-scheduling-spec".
Require Import job.
Require Import Coq.Lists.ListSet.

Definition schedule := Set.

Definition scheduled := set task -> schedule -> nat ->  Prop.

Definition cpu_platform := Set.

(* Restrictions on periodic task parameters *)
Record ident_mp (platform: cpu_platform) (num_cpus: nat) : Prop :=
  { a: 1 = 1 }.
