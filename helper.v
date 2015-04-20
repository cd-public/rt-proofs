Require Import Coq.Lists.List.

Lemma nat_seq_nth_In : forall len n, n < len -> In n (seq 0 len).
Proof. intros.
       assert (H1 := seq_nth).
       assert (H2 := H1 len 0 n len).
       assert (H3 := H).
       apply H2 in H. simpl in H.
       assert (nth_In := nth_In).
       assert (H4 := nth_In nat n (seq 0 len) len).
       assert (H5 := seq_length len 0).
       rewrite -> H5 in H4.
       apply H4 in H3.
       rewrite H in H3.
       trivial.
Qed.

Definition least_nat (n: nat) (P: nat -> Prop) : Prop :=
    P n /\ forall (n': nat), P n' -> n <= n'.

Definition greatest_nat (n: nat) (P: nat -> Prop) : Prop :=
    P n /\ forall (n': nat), P n' -> n' <= n.