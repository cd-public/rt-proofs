(******************************************************************************)
(* c11comp: Coq development attached to the paper                             *)
(*                                                                            *)
(*  Vafeiadis, Balabonski, Chakraborty, Morisset, and Zappa Nardelli.         *)
(*  Common compiler optimisations are invalid in the C11 memory model         *)
(*  and what we can do about it.                                              *)
(*  In POPL 2015.                                                             *)
(*                                                                            *)
(* Copyright (c) MPI-SWS and INRIA                                            *)
(* Released under a BSD-style license. See README.txt for details.            *)
(******************************************************************************)

Require Import List Permutation Vbase Classical.
Set Implicit Arguments.

Fixpoint flatten A (l: list (list A)) :=
  match l with 
    | nil => nil
    | x :: l' => x ++ flatten l'
  end.

Definition disjoint A (l1 l2 : list A) := 
  forall a (IN1: In a l1) (IN2: In a l2), False. 


Definition appA := app_assoc_reverse. 

(** Properties of [In] *)

Lemma In_eq : forall A (a:A) (l:list A), In a (a :: l).
Proof. vauto. Qed.

Lemma In_cons : forall A (a b:A) (l:list A), In b l -> In b (a :: l).
Proof. vauto. Qed.


Lemma In_nil : forall A (a:A), ~ In a nil.
Proof. by red. Qed.

Lemma In_split : forall A x (l:list A), In x l -> exists l1 l2, l = l1++x::l2.
Proof.
  induction l; simpl; intros; des; vauto.
  - exists nil; vauto.
  - destruct IHl; des; try done; eexists (_ :: _); vauto.
Qed.

Lemma In_dec :
  forall A (D: forall x y:A, {x = y} + {x <> y}) (a: A) l, {In a l} + {~ In a l}.
Proof.
  induction l; vauto; simpl; destruct (D a a0); intuition.
Qed.

Lemma In_appI1 : forall A (x:A) l (IN: In x l) l', In x (l++l').
Proof. induction l; ins; desf; eauto. Qed.

Lemma In_appI2 : forall A (x:A) l' (IN: In x l') l, In x (l++l').
Proof. induction l; ins; desf; eauto. Qed.

Lemma In_appD : forall A (x:A) l l' (IN: In x (l++l')), In x l \/ In x l'.
Proof. induction l; intuition. Qed.

Lemma In_app : forall A (x:A) l l', In x (l++l') <-> In x l \/ In x l'.
Proof. intuition; auto using In_appI1, In_appI2. Qed.

Lemma In_rev : forall A (x: A) l, In x (rev l) <-> In x l.
Proof.
  induction l; ins; rewrite In_app, IHl; ins; tauto.
Qed.

Lemma In_revI : forall A (x: A) l (IN: In x l), In x (rev l).
Proof. by intros; apply In_rev. Qed.

Lemma In_revD : forall A (x: A) l (IN: In x (rev l)), In x l.
Proof. by intros; apply In_rev. Qed.

Lemma In_mapI : forall A B (f: A -> B) x l (IN: In x l), In (f x) (map f l).
Proof. induction l; ins; intuition vauto. Qed.

Lemma In_mapD :
  forall A B (f: A->B) y l, In y (map f l) -> exists x, f x = y /\ In x l.
Proof.
  induction l; ins; intuition; des; eauto.
Qed.

Lemma In_map :
  forall A B (f: A->B) y l, In y (map f l) <-> exists x, f x = y /\ In x l.
Proof.
  split; intros; des; clarify; auto using In_mapI, In_mapD.
Qed.

Lemma In_filter :
  forall A (x:A) f l,  In x (filter f l) <-> In x l /\ f x.
Proof. induction l; ins; desf; simpls; intuition; clarify. Qed.

Lemma In_filterI :
  forall A x l (IN: In x l) (f: A->bool) (F: f x), In x (filter f l).
Proof. by intros; apply In_filter. Qed.

Lemma In_filterD :
  forall A (x:A) f l (D: In x (filter f l)), In x l /\ f x.
Proof. by intros; apply In_filter. Qed.

Lemma In_flatten A (x:A) l : 
  In x (flatten l) <-> exists y, In x y /\ In y l.
Proof.
  induction l; ins; rewrite ?In_app, ?IHl; clear; split; ins; desf; eauto.
Qed.

Hint Resolve In_eq In_cons In_appI1 In_appI2 In_mapI In_revI In_filterI : vlib.


Lemma nodup_one A (x: A) : NoDup (x :: nil).
Proof. vauto. Qed.

Hint Resolve NoDup_nil nodup_one.

Lemma nodup_map:
  forall (A B: Type) (f: A -> B) (l: list A),
  NoDup l ->
  (forall x y, In x l -> In y l -> x <> y -> f x <> f y) ->
  NoDup (map f l).
Proof.
  induction 1; ins; vauto. 
  constructor; eauto.
  intro; rewrite In_map in *; desf.
  edestruct H1; try eapply H2; eauto.
  intro; desf.
Qed.

Lemma nodup_append_commut:
  forall (A: Type) (a b: list A),
  NoDup (a ++ b) -> NoDup (b ++ a).
Proof.
  intro A.
  assert (forall (x: A) (b: list A) (a: list A), 
           NoDup (a ++ b) -> ~(In x a) -> ~(In x b) -> 
           NoDup (a ++ x :: b)).
    induction a; simpl; intros.
    constructor; auto.
    inversion H. constructor. red; intro.
    elim (in_app_or _ _ _ H6); intro.
    elim H4. apply in_or_app. tauto.
    elim H7; intro. subst a. elim H0. left. auto. 
    elim H4. apply in_or_app. tauto.
    auto.
  induction a; simpl; intros.
  rewrite <- app_nil_end. auto.
  inversion H0. apply H. auto. 
  red; intro; elim H3. apply in_or_app. tauto.
  red; intro; elim H3. apply in_or_app. tauto.
Qed.

Lemma nodup_cons A (x: A) l:
  NoDup (x :: l) <-> ~ In x l /\ NoDup l.
Proof. split; inversion 1; vauto. Qed.

Lemma nodup_app:
  forall (A: Type) (l1 l2: list A),
  NoDup (l1 ++ l2) <->
  NoDup l1 /\ NoDup l2 /\ disjoint l1 l2.
Proof.
  induction l1; ins. 
    by split; ins; desf; vauto.
  rewrite !nodup_cons, IHl1, In_app; unfold disjoint.
  ins; intuition (subst; eauto). 
Qed.

Lemma nodup_append:
  forall (A: Type) (l1 l2: list A),
  NoDup l1 -> NoDup l2 -> disjoint l1 l2 ->
  NoDup (l1 ++ l2).
Proof.
  generalize nodup_app; firstorder.
Qed.

Lemma nodup_append_right:
  forall (A: Type) (l1 l2: list A),
  NoDup (l1 ++ l2) -> NoDup l2.
Proof.
  generalize nodup_app; firstorder.
Qed.

Lemma nodup_append_left:
  forall (A: Type) (l1 l2: list A),
  NoDup (l1 ++ l2) -> NoDup l1.
Proof.
  generalize nodup_app; firstorder.
Qed.

Lemma NoDup_filter A (l: list A) (ND: NoDup l) f : NoDup (filter f l). 
Proof. 
  induction l; ins; inv ND; desf; eauto using NoDup.
  econstructor; eauto; rewrite In_filter; tauto.
Qed.

Hint Resolve NoDup_filter.

Lemma NoDup_eq_one A (x : A) l : 
   NoDup l -> In x l -> (forall y (IN: In y l), y = x) -> l = x :: nil.
Proof.
  destruct l; ins; f_equal; eauto.
  inv H; desf; clear H H5; induction l; ins; desf; case H4; eauto using eq_sym.
  rewrite IHl in H0; ins; desf; eauto.
Qed.

Lemma Permutation_NoDup A ( l l' : list A) : 
  Permutation l l' -> NoDup l -> NoDup l'.
Proof.
  induction 1; eauto; rewrite !nodup_cons in *; ins; desf; intuition. 
  eby symmetry in H; eapply H0; eapply Permutation_in.
Qed.

Lemma NoDup_mapD A B (f : A-> B) l :
  NoDup (map f l) -> NoDup l.
Proof.
  induction l; ins; rewrite !nodup_cons, In_map in *; desf; eauto 8.
Qed.

Lemma perm_from_subset : 
  forall A (l : list A) l',
    NoDup l' ->
    (forall x, In x l' -> In x l) ->
    exists l'', Permutation l (l' ++ l''). 
Proof.
  induction l; ins; vauto.
    by destruct l'; ins; vauto; exfalso; eauto.
  destruct (classic (In a l')).

    eapply In_split in H1; desf; rewrite ?nodup_app, ?nodup_cons in *; desf.
    destruct (IHl (l1 ++ l2)); ins. 
      by rewrite ?nodup_app, ?nodup_cons in *; desf; repeat split; ins; red; eauto using In_cons.
      by specialize (H0 x); rewrite In_app in *; ins; desf;
         destruct (classic (a = x)); subst; try tauto; exfalso; eauto using In_eq.
    eexists; rewrite appA in *; ins.
    by eapply Permutation_trans, Permutation_middle; eauto.

  destruct (IHl l'); eauto; ins.
    by destruct (H0 x); auto; ins; subst.
  by eexists (a :: _); eapply Permutation_trans, Permutation_middle; eauto.
Qed.

