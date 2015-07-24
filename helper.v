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

Lemma big_nat_split m n o F:
  forall (GE: o >= m) (LT: o <= n),
    \sum_(m <= i < n) F i =
      (\sum_(m <= i < o) F i) + (\sum_(o <= i < n) F i).
Proof.
  remember (o - m) as k.
  (*generalize dependent n. generalize dependent m.
  induction k; ins.
  {
    assert (o = m). ssromega. subst.
    by rewrite [\sum_(m <= i < m) _]big_geq //.
  }
  rewrite -addn1 in Heqk.
  assert (m <= o - 1). ssromega.
  apply IHk.
  ssromega.
  admit.*)
  generalize dependent m.
  induction o; ins.
  {
    move: GE; rewrite leqn0; move => /eqP GE; subst.
    by rewrite [\sum_(0 <= i < 0 | _) _]big_geq //.
  }
  {
    (*destruct m.*)
    rewrite big_nat_recr //. rewrite big_add1.
    rewrite -addnA. rewrite -big_nat_recl; last first.
Admitted.

(*Lemma telescoping_sum : forall (T: Type) F r (x0: T),
              F (nth x0 r (size r).-1) - F (nth x0 r 0) =
                \sum_(i < (size r).-1) (F (nth x0 r (i.+1)) - F (nth x0 r i)).
Proof.
  intros T F r x0.

  assert (forall (i j: nat) (LE: i <= j), F (nth x0 r i) <= F (nth x0 r j)).


  induction r.
    by rewrite subnn big_ord0.
    
  
  destruct r.
    by rewrite subnn big_ord0.
    induction r.
      by rewrite subnn big_ord0.
      
  
  generalize dependent r.
  induction r.
    by rewrite subnn big_ord0.
    ins.
    assert (r = behead (a :: r)). admit.
    exploit IHr. intros i j LE.
    rewrite H0.
    rewrite 2!nth_behead.
    apply H. ins.
    intro IH.
    rewrite H0 in IH.
    rewrite nth_behead in IH.
    destruct r.
      by rewrite subnn big_ord0.

    rewrite big_ord_recl; simpl in *.
    rewrite -IH.
    rewrite addnBA; last first.
    specialize (H 1 (size r)).
    exploit H; ins.
    unfold nth.

  -addnA.
      rewrite <- eqn_add2r with (p := F a).
      rewrite addnC. rewrite addnBA.
      exploit IHr.
      ins. destruct nth.
      unfold nth.
      destruct s.
 
        rewrite -eqn_add2r.
  destruct r.
    by rewrite subnn big_ord0.
  destruct r.
    by rewrite subnn big_ord0.
  induction r.
    simpl in *. rewrite big_ord_recl. simpl in *.
     by rewrite big_ord0 addn0.

    repeat rewrite big_ord_recl.
    simpl in *.
    rewrite big_ord_recl in IHr.
    simpl in *.
     induction r.
    by rewrite subnn big_ord0.
     rewrite -big_ord_recl.
  
  
  destruct r.
    by rewrite subnn big_ord0.
  
  induction r.
    by rewrite subnn big_ord0. 
    simpl in *.
    rewrite -> nth_last in *.
    rewrite -> last_cons in *.
    destruct r.
      by rewrite big_ord_recl big_ord0 addn0; simpl in *.
      simpl in *.
      rewrite IHr. simpl in *.

      rewrite big_ord_recl. rewrite big_ord_recl. rewrite big_ord_recl.
      simpl in *.
      rewrite addnA. simpl in *.
      rewrite [(_ - _) + (_ - _)]addnC.
      rewrite addnBA.

*)
