Require Import List Arith Classical Vbase.

Lemma no_elements_nil :
  forall (A: Type) (l: list A) (NOELEM: forall x, In x l -> False), l = nil.
Proof.
  ins; destruct l; trivial.
  by exfalso; apply (NOELEM a); left.
Qed.

Lemma length_comm :
  forall (A: Type) (l1 l2: list A) (SAME: forall x, In x l1 <-> In x l2),
    length l1 = length l2.
Proof.
  ins; remember (length l1) as len.
Admitted.

Lemma length_nil :
  forall (A: Type) (l: list A), length l = 0 <-> l = nil.
Proof.
  split; intro H; [| by rewrite H; simpl].
  destruct l; [by trivial | by simpl in *; inversion H].
Qed.

Lemma list_nonempty :
  forall (l: list nat), l <> nil <-> exists a, In a l.
Proof.
  split; intro H; des.
    destruct l.
      by trivial.
      by exists n; left.
    by unfold not; ins; subst; trivial.
Qed.

Lemma split_inclusion_helper :
  forall (A: Type) (l0 l1 l2 l3: list A) (a: A)
         (OR: In a l0 \/ In a l1)
         (ALL: forall x : A, In x (l0 ++ a :: l1) <-> In x (l2 ++ a :: l3)),
    In a l2 \/ In a l3.
Proof.
  ins. remember (length (l0 ++ a :: l1)) as len. 
  generalize dependent l1. generalize dependent l0.
  induction len; ins.
  {
    symmetry in Heqlen. apply length_nil in Heqlen.
    symmetry in Heqlen.
    exfalso. assert (NOTNIL := app_cons_not_nil).
    specialize (NOTNIL A l0 l1 a). intuition.
  }
  (* NOT ABLE TO PROVE THIS *)
Admitted.

Lemma split_inclusion :
  forall (A: Type) (l0 l1 l2 l3: list A) (a: A),
    (forall x : A, In x (l0 ++ l1) <-> In x (l2 ++ l3)) <->
    (forall x : A, In x (l0 ++ a :: l1) <-> In x (l2 ++ a :: l3)).
Proof.
  split; ins.
  {
    rewrite 2 in_app_iff in *.
    simpl in *.
    cut (In x l0 \/ In x l1 <-> In x l2 \/ In x l3); ins; [by tauto|].
    specialize (H x).
    by rewrite 2 in_app_iff in *.
  }
  {
    split; ins.
    {
      rewrite in_app_iff in *.
      assert (In x (l2 ++ a :: l3)).
        rewrite <- H; rewrite in_app_iff.
        destruct H0; [by left | by right; right].
      rewrite in_app_iff in H1.
      destruct H1; simpl in H1; [by left|].
        destruct H1; subst.
          by apply (split_inclusion_helper A l0 l1); eauto.
          by right.
    }
    {
      rewrite in_app_iff in *.
      assert (In x (l0 ++ a :: l1)).
        rewrite H; rewrite in_app_iff.
        destruct H0; [by left | by right; right].
      rewrite in_app_iff in H1.
      destruct H1; simpl in H1; [by left|].
        destruct H1; subst.
          by apply (split_inclusion_helper A l2 l3); ins; split; rewrite H.
          by right.
    }
  }
Qed.