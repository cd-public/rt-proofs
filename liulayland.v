Add LoadPath "/home/felipec/dev/coq/rt-scheduling-spec".
Require Import Coq.Lists.List.
Require Import job.
Require Import schedule.
Require Import identmp.

Section LiuLayland.
Variable sched: schedule.
Axiom uniprocessor : ident_mp 1 sched.
End LiuLayland.