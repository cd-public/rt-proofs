Add LoadPath "/home/felipec/dev/coq/rt-scheduling-spec".
Require Import Coq.Lists.List.
Require Import Coq.Arith.Lt.
Require Import job.
Require Import schedule.
Require Import identmp.
Require Import priority.
Require Import helper.

Section LiuLayland.
Variable ts: taskset.
Variable sched: schedule.
Variable hp: higher_priority.
Variable arr: arrival_seq.
Axiom RM_priority : fixed_priority hp RM.
Axiom uniprocessor : ident_mp 1 sched hp.
Axiom jobs_from_taskset: schedule_of sched ts.
Axiom arrival_sequence_from_taskset: ts_arrival_seq ts arr.

Lemma uni_simpler_invariant :
      forall (jlow : job) (t : time),
          backlogged jlow sched t
              <-> exists jhigh : job, hp jhigh jlow sched t /\ sched jhigh t = 1.
Proof.
  intros.
  assert (H1 := uniprocessor).
  split.
  intros.
  inversion H1.
  assert (H3 := ident_mp_invariant jlow t).
  inversion H3 as [H4 _]. clear H3 ident_mp_invariant ident_mp_cpus_nonzero. 
  edestruct ((H4 H) 0). apply le_lt_n_Sm. trivial.
  inversion H0 as [H5 H6].
  assert (H7 := element_in_list).
  specialize (H7 job x (cpumap sched t) 0 H6).
  specialize (ident_mp_mapping t ).
  inversion ident_mp_mapping as [_ H8].
  specialize (H8 x).
  inversion H8 as [H9 _].
  specialize (H9 H7).
  exists x. apply (conj H5 H9).
  
  intros. inversion H as [jhigh]. inversion H0.
  inversion H1.
  specialize (ident_mp_invariant jlow t).
  inversion ident_mp_invariant as [_ H4].
  apply H4.
  intros. exists jhigh. split. apply H2.
  specialize (ident_mp_mapping t).
  inversion ident_mp_mapping as [H6 H7].
  specialize (H7 jhigh).
  inversion H7 as [_ H8].
  apply H8 in H3.
  clear ident_mp_invariant ident_mp_sched_unit ident_mp_mapping ident_mp_cpus_nonzero H H0 H1 H2 H4 H7 H8.
  apply In_singleton_list with (x := jhigh); trivial.
Qed.

End LiuLayland.