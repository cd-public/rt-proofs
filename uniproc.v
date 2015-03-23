Add LoadPath "/home/felipec/dev/coq/rt-scheduling-spec".
Require Import job.
Require Import schedule.

Definition uniprocessor (s: schedule) := ident_mp 1 s.

Section LiuLayland.
  Variable tau : list periodic_task.
  Variable s : schedule.
  Axiom uniprocessor_schedule : uniprocessor s.

End LiuLayland.

Define critical_instant()

Section RM.

