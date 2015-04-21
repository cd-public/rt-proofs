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

Definition least_nat (n: nat) (P: nat -> Prop) : Prop :=
    P n /\ forall (n': nat), P n' -> n <= n'.

Definition greatest_nat (n: nat) (P: nat -> Prop) : Prop :=
    P n /\ forall (n': nat), P n' -> n' <= n.

Axiom excluded_middle : forall P: Prop, P \/ ~P.