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

(* Additional lemmas about max. *)
Section ExtraLemmas.
  
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
    
End ExtraLemmas.