Add LoadPath "/home/felipec/dev/coq/rt-scheduling-spec".
Require Import Coq.Lists.List.
Require Import job.
Require Import schedule.
Require Import identmp.
Require Import priority.

Section LiuLayland.
Variable sched: schedule.
Variable hp: higher_priority.
Axiom RM_priority : fixed_priority hp RM.
Axiom uniprocessor : ident_mp 1 sched hp.

Lemma uni_simpler_invariant : forall (jlow : job) (t : time),
                backlogged jlow sched t <-> exists ! jhigh : job, sched jhigh t = 1.
Proof.
  intros.
  assert (H1 := uniprocessor).
  split.
  intros. unfold backlogged in H. inversion H.
  inversion H1.
  assert (H3 := ident_mp_invariant jlow t).
  inversion H3.


End LiuLayland.