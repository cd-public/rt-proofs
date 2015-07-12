Require Import Vbase List Classical helper.

Definition list_sum (l: list nat) := fold_right plus 0 l.

Lemma sum_list_max_bound :
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

Lemma sum_list_app :
  forall (l1 l2: list nat),
    list_sum (l1 ++ l2) = list_sum l1 + list_sum l2.
Proof.
  induction l1; [by trivial|]; ins.
    destruct l2.
      by simpl; rewrite app_nil_r; rewrite <- plus_n_O.
      by rewrite IHl1; simpl; omega. 
Qed.

Lemma sum_list_comm :
  forall (l1 l2: list nat) (SAME: forall x, In x l1 <-> In x l2),
    list_sum l1 = list_sum l2.
Proof.
  ins; remember (length l1) as len.
  assert (Heqlen2: len = length l2).
    by rewrite <- length_comm with (l1 := l1).
  generalize dependent l2.
  generalize dependent l1.
  generalize dependent len. 
  induction len; ins; simpl in *.
    (* Base case : empty list *)
    by symmetry in Heqlen, Heqlen2; rewrite length_nil in *; subst; simpl.
    (* Inductive Step *)
    assert (exists a, In a l1); des.
      by apply list_nonempty; unfold not; ins; subst; simpl in *.
    assert (In a l2). by rewrite <- SAME.
    apply in_split in H0; apply in_split in H; des; subst.
    rewrite 2 sum_list_app; simpl.
    rewrite app_length in *. simpl in *.
    rewrite <- plus_n_Sm in *.
    inversion Heqlen. inversion Heqlen2.
    rewrite <- app_length in *.
    rewrite <- split_inclusion in SAME.
    cut (list_sum l4 + list_sum l5 = list_sum l0 + list_sum l3); ins; [by omega|].
    rewrite <- 2 sum_list_app; eauto using IHlen.
Qed.

Lemma sum_list_partition :
  forall (l l1 l2: list nat)
         f (PART: partition f l = (l1, l2)),
    list_sum l = list_sum l1 + list_sum l2.
Proof.
  ins.
  rewrite <- sum_list_app.
  apply sum_list_comm.
Admitted.