Require Import rt.util.tactics rt.util.notation rt.util.sorting rt.util.nat.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop path.

(* Lemmas about arithmetic with sums. *)
Section SumArithmetic.

  (* Inequality with sums is monotonic with their functions. *)
  Lemma sum_diff_monotonic :
    forall n G F,
      (forall i : nat, i < n -> G i <= F i) ->
      (\sum_(0 <= i < n) (G i)) <= (\sum_(0 <= i < n) (F i)).
  Proof.
    intros n G F ALL.
    rewrite big_nat_cond [\sum_(0 <= i < n) F i]big_nat_cond.
    apply leq_sum; intros i LT; rewrite andbT in LT.
    move: LT => /andP LT; des.
    by apply ALL, leq_trans with (n := n); ins.
  Qed.

  Lemma sum_diff :
    forall n F G,
      (forall i (LT: i < n), F i >= G i) ->
      \sum_(0 <= i < n) (F i - G i) =
        (\sum_(0 <= i < n) (F i)) - (\sum_(0 <= i < n) (G i)).       
  Proof.
    intros n F G ALL.
    induction n; ins; first by rewrite 3?big_geq.
    assert (ALL': forall i, i < n -> G i <= F i).
      by ins; apply ALL, leq_trans with (n := n); ins.
    rewrite 3?big_nat_recr // IHn //; simpl.
    rewrite subh1; last by apply sum_diff_monotonic.
    rewrite subh2 //; try apply sum_diff_monotonic; ins.
    rewrite subh1; ins; apply sum_diff_monotonic; ins.
    by apply ALL; rewrite ltnS leqnn. 
  Qed.

  Lemma telescoping_sum :
    forall (T: Type) (F: T->nat) r (x0: T),
    (forall i, i < (size r).-1 -> F (nth x0 r i) <= F (nth x0 r i.+1)) ->
      F (nth x0 r (size r).-1) - F (nth x0 r 0) =
        \sum_(0 <= i < (size r).-1) (F (nth x0 r (i.+1)) - F (nth x0 r i)).
  Proof.
    intros T F r x0 ALL.
    have ADD1 := big_add1.
    have RECL := big_nat_recl.
    specialize (ADD1 nat 0 addn 0 (size r) (fun x => true) (fun i => F (nth x0 r i))).
    specialize (RECL nat 0 addn (size r).-1 0 (fun i => F (nth x0 r i))).
    rewrite sum_diff; last by ins.
    rewrite addmovr; last by rewrite -[_.-1]add0n; apply prev_le_next; try rewrite add0n leqnn.
    rewrite subh1; last by apply sum_diff_monotonic.
    rewrite addnC -RECL //.
    rewrite addmovl; last by rewrite big_nat_recr // -{1}[\sum_(_ <= _ < _) _]addn0; apply leq_add.
    by rewrite addnC -big_nat_recr.
  Qed.

  Lemma leq_sum_sub_uniq :
    forall (T: eqType) (r1 r2: seq T) F,
      uniq r1 ->
      {subset r1 <= r2} ->
      \sum_(i <- r1) F i <= \sum_(i <- r2) F i.
  Proof.
    intros T r1 r2 F UNIQ SUB; generalize dependent r2.
    induction r1 as [| x r1' IH]; first by ins; rewrite big_nil.
    {
      intros r2 SUB.
      assert (IN: x \in r2).
        by apply SUB; rewrite in_cons eq_refl orTb.
      simpl in UNIQ; move: UNIQ => /andP [NOTIN UNIQ]; specialize (IH UNIQ).
      destruct (splitPr IN).
      rewrite big_cat 2!big_cons /= addnA [_ + F x]addnC -addnA leq_add2l.
      rewrite mem_cat in_cons eq_refl in IN.
      rewrite -big_cat /=.
      apply IH; red; intros x0 IN0.
      rewrite mem_cat.
      feed (SUB x0); first by rewrite in_cons IN0 orbT.
      rewrite mem_cat in_cons in SUB.
      move: SUB => /orP [SUB1 | /orP [/eqP EQx | SUB2]];
        [by rewrite SUB1 | | by rewrite SUB2 orbT].
      by rewrite -EQx IN0 in NOTIN.
    }
  Qed.
    
End SumArithmetic.
