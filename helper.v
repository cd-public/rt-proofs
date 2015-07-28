Require Import Vbase ssreflect ssrbool eqtype ssrnat seq fintype bigop ssromega.

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

Lemma subh1 : forall m n p (GE: m >= n), m - n + p = m + p - n.
Proof.
  by ins; ssromega.
Qed.

Lemma subh2 : forall m1 m2 n1 n2 (GE1: m1 >= m2) (GE2: n1 >= n2),
  (m1 + n1) - (m2 + n2) = m1 - m2 + (n1 - n2).
Proof.
  by ins; ssromega.
Qed.

Lemma subh3 : forall m n p (GE1: m + p <= n) (GE: n >= p),
                    (m <= n - p).
Proof.
  ins. rewrite <- leq_add2r with (p := p).
  by rewrite subh1 // -addnBA // subnn addn0.
Qed.

Lemma addmovr: forall m n p (GE: m >= n), m - n = p <-> m = p + n.
Proof.
  split; ins; ssromega.
Qed.

Lemma addmovl: forall m n p (GE: m >= n), p = m - n <-> p + n = m.
Proof.
  split; ins; ssromega.
Qed.

Lemma sum_diff_monotonic :
  forall n G F (ALL: forall i : nat, i < n -> G i <= F i),
    (\sum_(0 <= i < n) (G i)) <= (\sum_(0 <= i < n) (F i)).
Proof.
  ins; rewrite big_nat_cond [\sum_(0 <= i < n) F i]big_nat_cond.
  apply leq_sum; intros i LT; rewrite andbT in LT.
  move: LT => /andP LT; des.
  apply ALL, leq_trans with (n := n); ins.
Qed.

Lemma sum_diff : forall n F G (ALL: forall i (LT: i < n), F i >= G i),
    \sum_(0 <= i < n) (F i - G i) =
    (\sum_(0 <= i < n) (F i)) -
    (\sum_(0 <= i < n) (G i)).       
Proof.
  induction n; ins; first by rewrite 3?big_geq.
  assert (ALL': forall i, i < n -> G i <= F i).
    by ins; apply ALL, leq_trans with (n := n); ins.
  rewrite 3?big_nat_recr // IHn //; simpl.
  rewrite subh1; last by apply sum_diff_monotonic.
  rewrite subh2 //; try apply sum_diff_monotonic; ins.
  rewrite subh1; ins; apply sum_diff_monotonic; ins.
  by apply ALL; rewrite ltnS leqnn. 
Qed.

Lemma first_le_last :
  forall (T: Type) (F: T->nat) r (x0: T)
  (ALL: forall i, i < (size r).-1 -> F (nth x0 r i) <= F (nth x0 r i.+1)), 
    F (nth x0 r 0) <= (F (nth x0 r (size r).-1)).
Proof.
  intros T F r x0 ALL.
  generalize dependent r.
  induction r; first by simpl; rewrite leqnn.
  intros ALL.
Admitted.

Lemma telescoping_sum :
  forall (T: Type) (F: T->nat) r (x0: T)
  (ALL: forall i, i < (size r).-1 -> F (nth x0 r i) <= F (nth x0 r i.+1)), 
    F (nth x0 r (size r).-1) - F (nth x0 r 0) =
      \sum_(0 <= i < (size r).-1) (F (nth x0 r (i.+1)) - F (nth x0 r i)).
Proof.
  intros T F r x0 ALL.
  have ADD1 := big_add1.
  have RECL := big_nat_recl.
  specialize (ADD1 nat 0 addn 0 (size r) (fun x => true) (fun i => F (nth x0 r i))).
  specialize (RECL nat 0 addn (size r).-1 0 (fun i => F (nth x0 r i))).
  rewrite sum_diff; last by ins.
  rewrite addmovr; last by apply first_le_last.
  rewrite subh1; last by apply sum_diff_monotonic.
  rewrite addmovl; last first.
  {
    rewrite -[\sum_(0 <= i < _) F _]addn0.
    apply leq_add; last by ins.
    apply sum_diff_monotonic; last by ins.
  }
  rewrite addnC -big_nat_recr // -ADD1 addnC ADD1 -RECL //.
Qed.