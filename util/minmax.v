Require Import rt.util.tactics rt.util.notation rt.util.sorting rt.util.nat.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Section MinMaxSeq.

  Section Arg.
    
    Context {T: eqType}.

    Variable F: T -> nat.
    
    Fixpoint seq_argmax (F: T -> nat) (l: seq T) :=
      if l is x :: l' then
        if seq_argmax F l' is Some y then
          if F x >= F y then Some x else Some y
        else Some x
      else None.

    Fixpoint seq_argmin (F: T -> nat) (l: seq T) :=
      if l is x :: l' then
        if seq_argmin F l' is Some y then
          if F x <= F y then Some x else Some y
        else Some x
      else None.

    Section Lemmas.

      Lemma seq_max_exists:
        forall l x,
          x \in l ->
          seq_argmax F l != None.
      Proof.
        induction l; first by done.
        intros x; rewrite in_cons.
        move => /orP [/eqP EQ | IN] /=;
          first by subst; destruct (seq_argmax F l); first by case: ifP.
        by destruct (seq_argmax F l); first by case: ifP.
      Qed.
        
      Lemma mem_seq_max:
        forall l x,
          seq_argmax F l = Some x ->
          x \in l.
      Proof.
        induction l; simpl; first by done.
        intros x ARG.
        destruct (seq_argmax F l);
          last by case: ARG => EQ; subst; rewrite in_cons eq_refl.
        destruct (F s <= F a);
          first by case: ARG => EQ; subst; rewrite in_cons eq_refl.
        case: ARG => EQ; subst.
        by rewrite in_cons; apply/orP; right; apply IHl.
      Qed.

      Lemma seq_max_computes_max:
        forall l x y,
          seq_argmax F l = Some x ->
          y \in l ->
          F x >= F y.
      Proof.
        induction l; first by done.
        intros x y EQmax IN; simpl in EQmax.
        rewrite in_cons in IN.
        move: IN => /orP [/eqP EQ | IN].
        {
          subst.
          destruct (seq_argmax F l) eqn:ARG;
            last by case: EQmax => EQ; subst.
          destruct (leqP (F s) (F a)) as [LE | GT];
            first by case: EQmax => EQ; subst.
          apply leq_trans with (n := F s); first by apply ltnW.
          apply IHl; first by done.
          by apply mem_seq_max.
        }
        { 
          destruct (seq_argmax F l) eqn:ARG.
          {
            destruct (leqP (F s) (F a)) as [LE | GT];
              last by case: EQmax => EQ; subst; apply IHl.
            case: EQmax => EQ; subst.
            by apply: (leq_trans _ LE); apply IHl.
          }
          {
            case: EQmax => EQ; subst.
            by apply seq_max_exists in IN; rewrite ARG in IN.
          }
        }
      Qed.

      Lemma seq_min_exists:
        forall l x,
          x \in l ->
          seq_argmin F l != None.
      Proof.
        induction l; first by done.
        intros x; rewrite in_cons.
        move => /orP [/eqP EQ | IN] /=;
          first by subst; destruct (seq_argmin F l); first by case: ifP.
        by destruct (seq_argmin F l); first by case: ifP.
      Qed.
        
      Lemma mem_seq_min:
        forall l x,
          seq_argmin F l = Some x ->
          x \in l.
      Proof.
        induction l; simpl; first by done.
        intros x ARG.
        destruct (seq_argmin F l);
          last by case: ARG => EQ; subst; rewrite in_cons eq_refl.
        destruct (F s >= F a);
          first by case: ARG => EQ; subst; rewrite in_cons eq_refl.
        case: ARG => EQ; subst.
        by rewrite in_cons; apply/orP; right; apply IHl.
      Qed.

      Lemma seq_min_computes_min:
        forall l x y,
          seq_argmin F l = Some x ->
          y \in l ->
          F x <= F y.
      Proof.
        induction l; first by done.
        intros x y EQmin IN; simpl in EQmin.
        rewrite in_cons in IN.
        move: IN => /orP [/eqP EQ | IN].
        {
          subst; destruct (seq_argmin F l) eqn:ARG;
            last by case: EQmin => EQ; subst.
          destruct (ltnP (F s) (F a)) as [LT | GE];
            last by case: EQmin => EQ; subst.
          apply leq_trans with (n := F s); last by apply ltnW.
          apply IHl; first by done.
          by apply mem_seq_min.
        }
        { 
          destruct (seq_argmin F l) eqn:ARG.
          {
            destruct (ltnP (F s) (F a)) as [LT | GE];
              first by case: EQmin => EQ; subst; apply IHl.
            case: EQmin => EQ; subst.
            by apply: (leq_trans GE); apply IHl.
          }
          {
            case: EQmin => EQ; subst.
            by apply seq_min_exists in IN; rewrite ARG in IN.
          }
        }
      Qed.
      
    End Lemmas.
    
  End Arg.
  
  Definition seq_max := seq_argmax id.
  Definition seq_min := seq_argmin id.
  
End MinMaxSeq.

(* Additional lemmas about sum and max big operators. *)
Section ExtraLemmasSumMax.
  
  Lemma leq_big_max I r (P : pred I) (E1 E2 : I -> nat) :
    (forall i, P i -> E1 i <= E2 i) ->
      \max_(i <- r | P i) E1 i <= \max_(i <- r | P i) E2 i.
  Proof.
    move => leE12; elim/big_ind2 : _ => // m1 m2 n1 n2.
    intros LE1 LE2; rewrite leq_max; unfold maxn.
    by destruct (m2 < n2) eqn:LT; [by apply/orP; right | by apply/orP; left].
  Qed.

  Lemma bigmax_ord_ltn_identity n :
    n > 0 ->
    \max_(i < n) i < n.
  Proof.
    intros LT.
    destruct n; first by rewrite ltn0 in LT.
    clear LT.
    induction n; first by rewrite big_ord_recr /= big_ord0 maxn0.
    rewrite big_ord_recr /=.
    unfold maxn at 1; desf.
    by apply leq_trans with (n := n.+1).
  Qed.
    
  Lemma bigmax_ltn_ord n (P : pred nat) (i0: 'I_n) :
    P i0 ->
    \max_(i < n | P i) i < n.
  Proof.
    intros LT.
    destruct n; first by destruct i0 as [i0 P0]; move: (P0) => P0'; rewrite ltn0 in P0'.
    rewrite big_mkcond.
    apply leq_ltn_trans with (n := \max_(i < n.+1) i).
    {
      apply/bigmax_leqP; ins.
      destruct (P i); last by done.
      by apply leq_bigmax_cond.
    }
    by apply bigmax_ord_ltn_identity.
  Qed.

  Lemma bigmax_pred n (P : pred nat) (i0: 'I_n) :
    P (i0) ->
    P (\max_(i < n | P i) i).
  Proof.
    intros PRED.
    induction n.
    {
      destruct i0 as [i0 P0].
      by move: (P0) => P1; rewrite ltn0 in P1. 
    }
    rewrite big_mkcond big_ord_recr /=; desf.
    {
      destruct n; first by rewrite big_ord0 maxn0.
      unfold maxn at 1; desf.
      exfalso.
      apply negbT in Heq0; move: Heq0 => /negP BUG.
      apply BUG. 
      apply leq_ltn_trans with (n := \max_(i < n.+1) i).
      {
        apply/bigmax_leqP; ins.
        destruct (P i); last by done.
        by apply leq_bigmax_cond.
      }
      by apply bigmax_ord_ltn_identity.
    }
    {
      rewrite maxn0.
      rewrite -big_mkcond /=.
      have LT: i0 < n.
      {
        rewrite ltn_neqAle; apply/andP; split;
          last by rewrite -ltnS; apply ltn_ord.
        apply/negP; move => /eqP BUG.
        by rewrite -BUG PRED in Heq.
      }
      by rewrite (IHn (Ordinal LT)).
    }
  Qed.
  
  Lemma sum_nat_eq0_nat (T : eqType) (F : T -> nat) (r: seq T) :
    all (fun x => F x == 0) r = (\sum_(i <- r) F i == 0).
  Proof.
    destruct (all (fun x => F x == 0) r) eqn:ZERO.
    {
      move: ZERO => /allP ZERO; rewrite -leqn0.
      rewrite big_seq_cond (eq_bigr (fun x => 0));
        first by rewrite big_const_seq iter_addn mul0n addn0 leqnn.
      intro i; rewrite andbT; intros IN.
      specialize (ZERO i); rewrite IN in ZERO.
      by move: ZERO => /implyP ZERO; apply/eqP; apply ZERO.
    }
    {
      apply negbT in ZERO; rewrite -has_predC in ZERO.
      move: ZERO => /hasP ZERO; destruct ZERO as [x IN NEQ]; simpl in NEQ.
      rewrite (big_rem x) /=; last by done.
      symmetry; apply negbTE; rewrite neq_ltn; apply/orP; right.
      apply leq_trans with (n := F x); last by apply leq_addr.
      by rewrite lt0n.
    }
  Qed.
  
  Lemma extend_sum :
    forall t1 t2 t1' t2' F,
      t1' <= t1 ->
      t2 <= t2' ->
      \sum_(t1 <= t < t2) F t <= \sum_(t1' <= t < t2') F t.
  Proof.
    intros t1 t2 t1' t2' F LE1 LE2.
    destruct (t1 <= t2) eqn:LE12;
      last by apply negbT in LE12; rewrite -ltnNge in LE12; rewrite big_geq // ltnW.
    rewrite -> big_cat_nat with (m := t1') (n := t1); try (by done); simpl;
      last by apply leq_trans with (n := t2).
    rewrite -> big_cat_nat with (p := t2') (n := t2); try (by done); simpl.
    by rewrite addnC -addnA; apply leq_addr.
  Qed.

  Lemma leq_sum_nat m n (P : pred nat) (E1 E2 : nat -> nat) :
    (forall i, m <= i < n -> P i -> E1 i <= E2 i) ->
    \sum_(m <= i < n | P i) E1 i <= \sum_(m <= i < n | P i) E2 i.
  Proof.
    intros LE.
    rewrite big_nat_cond [\sum_(_ <= _ < _| P _)_]big_nat_cond.
    by apply leq_sum; move => j /andP [IN H]; apply LE.
  Qed.

  Lemma leq_sum_seq (I: eqType) (r: seq I) (P : pred I) (E1 E2 : I -> nat) :
    (forall i, i \in r -> P i -> E1 i <= E2 i) ->
    \sum_(i <- r | P i) E1 i <= \sum_(i <- r | P i) E2 i.
  Proof.
    intros LE.
    rewrite big_seq_cond [\sum_(_ <- _| P _)_]big_seq_cond.
    by apply leq_sum; move => j /andP [IN H]; apply LE.
  Qed.

  Lemma leq_sum1_smaller_range m n (P Q: pred nat) a b:
    (forall i, m <= i < n /\ P i -> a <= i < b /\ Q i) ->
    \sum_(m <= i < n | P i) 1 <= \sum_(a <= i < b | Q i) 1.
  Proof.
    intros REDUCE.
    rewrite big_mkcond.
    apply leq_trans with (n := \sum_(a <= i < b | Q i) \sum_(m <= i' < n | i' == i) 1).
    {
      rewrite (exchange_big_dep (fun x => true)); [simpl | by done].
      apply leq_sum_nat; intros i LE _.
      case TRUE: (P i); last by done.
      move: (REDUCE i (conj LE TRUE)) => [LE' TRUE'].
      rewrite (big_rem i); last by rewrite mem_index_iota.
      by rewrite TRUE' eq_refl.
    }
    {
      apply leq_sum_nat; intros i LE TRUE.
      rewrite big_mkcond /=.
      destruct (m <= i < n) eqn:LE'; last first.
      {
        rewrite big_nat_cond big1; first by done.
        move => i' /andP [LE'' _]; case EQ: (_ == _); last by done.
        by move: EQ => /eqP EQ; subst; rewrite LE'' in LE'.
      }
      rewrite (bigD1_seq i) /=; [ | by rewrite mem_index_iota | by rewrite iota_uniq ].
      rewrite eq_refl big1; first by done.
      by move => i' /negbTE NEQ; rewrite NEQ.
    }
  Qed.

End ExtraLemmasSumMax.

(*Section ProvingFinType.
    
    Lemma seq_sub_choiceMixin : choiceMixin (seq_sub l).
    Proof.
      destruct (seq_sub_enum l) eqn:SUB.
      {
        set f := fun (P: pred (seq_sub l)) (x: nat) => @None (seq_sub l).
                 exists f; last by done.
                 {
                   intros P n x.
                   have IN := mem_seq_sub_enum x.
                     by rewrite SUB in_nil in IN.
                 }
                 {
                   move => P [x PROP].
                   have IN := mem_seq_sub_enum x.
                     by rewrite SUB in_nil in IN.
                 }
      }
      {
        set NTH := nth s (seq_sub_enum l).
        set f := fun (P: pred (seq_sub l)) (x: nat) => if P (NTH x) then Some (NTH x) else None.
        exists f.
        {
          unfold f; intros P n x.
          by case: ifP => [PROP | //]; case => <-.
        }
        {
          move => P [x PROP].
          exists (index x (seq_sub_enum l)).
          by rewrite /f /NTH nth_index ?PROP; last by apply mem_seq_sub_enum.
        }
        {
          by intros P Q EQ x; rewrite /f -EQ.
        }
      }
    Qed.

    Canonical seq_sub_choiceType :=
      Eval hnf in ChoiceType (seq_sub l) (seq_sub_choiceMixin).  
    

    Definition seq_sub_countMixin' := CountMixin (@seq_sub_pickleK T l).

    Canonical seq_sub_countType := @Countable.pack _ seq_sub_countMixin' seq_sub_choiceType _ id.


    Lemma seq_sub_enumP: Finite.axiom (seq_sub_enum l).
    Proof.
      intros x.
      rewrite count_uniq_mem ?undup_uniq //.
      by apply/eqP; rewrite eqb1; apply mem_seq_sub_enum.
    Qed.
  
    Definition seq_sub_finMixin := @FinMixin seq_sub_countType (seq_sub_enum l) seq_sub_enumP.

    Canonical seq_sub_finType :=
      @Finite.pack (seq_sub l) [eqMixin of (seq_sub l)] seq_sub_finMixin seq_sub_choiceType _ id _ id. 

  End ProvingFinType.*)

