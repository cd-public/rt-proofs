Require Import Vbase ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Reserved Notation "\cat_ ( m <= i < n ) F"
  (at level 41, F at level 41, i, m, n at level 50,
   format "'[' \cat_ ( m <= i < n ) '/ ' F ']'").

Notation "\cat_ ( m <= i < n ) F" :=
  (\big[cat/[::]]_(m <= i < n) F%N) : nat_scope.

Lemma exists_inP_nat t (P: nat -> bool):
  reflect (exists x, x < t /\ P x) [exists (x | x \in 'I_t), P x].
Proof.
  destruct [exists x0 in 'I_t, P x0] eqn:EX; [apply ReflectT | apply ReflectF]; ins.
    move: EX => /exists_inP EX; des.
    by exists x; split; [by apply ltn_ord |].

    apply negbT in EX; rewrite negb_exists_in in EX.
    move: EX => /forall_inP ALL.
    unfold not; ins; des.
    specialize (ALL (Ordinal H)).
    by exploit ALL; unfold negb; try rewrite H0.
Qed.

Lemma exists_inPQ_nat t (P Q: nat -> bool):
  reflect (exists x, x < t /\ P x /\ Q x) [exists (x | x \in 'I_t), P x && Q x].
Proof.
  destruct [exists x0 in 'I_t, P x0 && Q x0] eqn:EX; [apply ReflectT | apply ReflectF]; ins.
    move: EX => /exists_inP EX; des.
    move: H2 => /andP H2; des.
    by exists x; split; [by apply ltn_ord |].

    apply negbT in EX; rewrite negb_exists_in in EX.
    move: EX => /forall_inP ALL.
    unfold not; ins; des.
    specialize (ALL (Ordinal H)).
    by exploit ALL; unfold negb; try rewrite H0 H1.
Qed.