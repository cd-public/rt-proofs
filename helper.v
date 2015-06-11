Require Import List Arith Vbase.

Lemma nat_seq_nth_In : forall n len (LT: n < len), In n (seq 0 len).
Proof.
  ins.
  assert (NTH := seq_nth).
  generalize LT; apply NTH with (start := 0) (d := len) in LT; simpl in LT; ins.
  assert (NTHIn := nth_In).
  specialize (NTHIn nat n (seq 0 len) len).
  rewrite (seq_length len 0), LT in NTHIn.
  eauto.
Qed.
  
Lemma In_singleton_list :
    forall (A: Type) (x: A) l n, In (Some x) l -> n < 1 -> length l = 1 -> nth n l None = Some x.
Proof.
  intros.
  destruct n; [|inversion H0; inversion H3].
  destruct l; [inversion H1|].
  destruct l; [|inversion H1].
  destruct H; [|contradiction].
  auto.
Qed.

Lemma element_in_list : forall (A: Type) (x: A) (l: list (option A)) (n: nat),
                            nth n l None = Some x -> In (Some x) l.
Proof.
    intros. assert (H1 := nth_in_or_default).
    specialize (H1 (option A) n l None).
    inversion H1. rewrite <- H. apply H0.
    rewrite H in H0. inversion H0.
Qed.

Lemma element_in_list_no_overflow :
    forall (A: Type) (x: A) (l: list (option A)) (n: nat),
        nth n l None = Some x -> n < length l.
Proof.
Admitted.

Definition least_nat (n: nat) (P: nat -> Prop) : Prop :=
    P n /\ forall (n': nat), P n' -> n <= n'.

Definition greatest_nat (n: nat) (P: nat -> Prop) : Prop :=
    P n /\ forall (n': nat), P n' -> n' <= n.

Lemma not_gt_le : forall n m : nat, ~ n > m -> n <= m.
Proof. by ins; omega. Qed.