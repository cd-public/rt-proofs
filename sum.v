Require Import Vbase List Classical.

Definition list_sum (l: list nat) := fold_right plus 0 l.

Lemma sum_max :
  forall (l: list nat) (max: nat)
         (MAX: forall x (IN: In x l), x <= max),
    list_sum l <= (length l) * max.
Proof.
  ins; remember (length l) as len.
  generalize dependent l.
  induction len; ins.
    destruct l.
      by eauto.
      by simpl in Heqlen; intuition.
    destruct l.
      by intuition.  
      {
        unfold list_sum; simpl.
        cut (fold_right plus 0 l <= len * max); ins.
          by assert (n <= max); [by apply MAX; left|]; omega.
        apply IHlen; eauto.
      }
Qed.

Lemma no_elements_nil :
  forall {X: Type} (l: list X) (NOELEM: forall x, In x l -> False), l = nil.
Proof.
  ins; destruct l; trivial.
  by exfalso; apply (NOELEM x); left.
Qed.

Lemma sum_commutative2 :
  forall (l1 l2: list nat) (SAME: forall x, In x l1 <-> In x l2),
    length l1 = length l2.
Proof.
  ins.
Admitted.


Lemma sum_commutative :
  forall (l1 l2: list nat) (SAME: forall x, In x l1 <-> In x l2),
    list_sum l1 = list_sum l2.
Proof.
  ins; remember (length l1) as len1; remember (length l2) as len2.
  generalize dependent l2. generalize dependent l1.
  induction len1; ins.
  admit.
  destruct l1; [by intuition|].
  destruct l2.
Admitted.