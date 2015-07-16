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

(******************************************************************************)
(** * Basic properties of relations *)
(******************************************************************************)

Require Import Vbase List Relations Classical. 
Set Implicit Arguments.

(** Definitions of relations *)
(******************************************************************************)

Definition immediate X (rel : relation X) (a b: X) :=
  rel a b /\ (forall c (R1: rel a c) (R2: rel c b), False).

Definition irreflexive X (rel : relation X) := forall x, rel x x -> False.

Definition asymmetric X (rel : relation X) := forall x y, rel x y /\ rel y x -> False.

Definition acyclic X (rel : relation X) := irreflexive (clos_trans X rel).

Definition is_total X (cond: X -> Prop) (rel: relation X) :=
  forall a (IWa: cond a)
         b (IWb: cond b) (NEQ: a <> b),
    rel a b \/ rel b a.

Definition restr_subset X (cond: X -> Prop) (rel rel': relation X) :=
  forall a (IWa: cond a)
         b (IWb: cond b) (REL: rel a b),
    rel' a b.

Definition restr_rel X (cond : X -> Prop) (rel : relation X) : relation X :=
  fun a b => rel a b /\ cond a /\ cond b.

Definition restr_eq_rel A B (f : A -> B) rel x y :=
  rel x y /\ f x = f y.

Definition upward_closed (X: Type) (rel: relation X) (P: X -> Prop) :=
  forall x y (REL: rel x y) (POST: P y), P x.

Definition max_elt (X: Type) (rel: relation X) (a: X) :=
  forall b (REL: rel a b), False.

Notation "r 'UNION1' ( a , b )" := 
  (fun x y => x = a /\ y = b \/ r x y) (at level 100). 

Notation "a <--> b" := (same_relation _ a b)  (at level 110).


(** Very basic properties of relations *)
(******************************************************************************)


Lemma clos_trans_mon A (r r' : relation A) a b :
  clos_trans A r a b ->
  (forall a b, r a b -> r' a b) ->
  clos_trans A r' a b.
Proof.
  induction 1; ins; eauto using clos_trans.
Qed.

Lemma clos_refl_trans_mon A (r r' : relation A) a b :
  clos_refl_trans A r a b ->
  (forall a b, r a b -> r' a b) ->
  clos_refl_trans A r' a b.
Proof.
  induction 1; ins; eauto using clos_refl_trans.
Qed.


Lemma clos_refl_transE A r a b :
  clos_refl_trans A r a b <-> a = b \/ clos_trans A r a b.
Proof.
  split; ins; desf; vauto; induction H; desf; vauto. 
Qed.

Lemma clos_trans_in_rt A r a b :
  clos_trans A r a b -> clos_refl_trans A r a b.
Proof.
  induction 1; vauto. 
Qed.

Lemma rt_t_trans A r a b c :
  clos_refl_trans A r a b -> clos_trans A r b c -> clos_trans A r a c.
Proof.
  ins; induction H; eauto using clos_trans. 
Qed.

Lemma t_rt_trans A r a b c :
  clos_trans A r a b -> clos_refl_trans A r b c -> clos_trans A r a c.
Proof.
  ins; induction H0; eauto using clos_trans. 
Qed.


Lemma t_step_rt A R x y : 
  clos_trans A R x y <-> exists z, R x z /\ clos_refl_trans A R z y.
Proof.
  split; ins; desf.
    by apply clos_trans_tn1 in H; induction H; desf; eauto using clos_refl_trans.
  by rewrite clos_refl_transE in *; desf; eauto using clos_trans.
Qed.

Lemma t_rt_step A R x y : 
  clos_trans A R x y <-> exists z, clos_refl_trans A R x z /\ R z y.
Proof.
  split; ins; desf.
    by apply clos_trans_t1n in H; induction H; desf; eauto using clos_refl_trans.
  by rewrite clos_refl_transE in *; desf; eauto using clos_trans.
Qed.

Lemma clos_trans_of_transitive A R (T: transitive A R) x y : 
  clos_trans A R x y -> R x y.
Proof.
  induction 1; eauto.
Qed.

Lemma clos_trans_eq :
  forall X (rel: relation X) Y (f : X -> Y) 
         (H: forall a b (SB: rel a b), f a = f b) a b
         (C: clos_trans _ rel a b),
    f a = f b.
Proof.
  ins; induction C; eauto; congruence.
Qed.

Lemma trans_irr_acyclic : 
  forall A R, irreflexive R -> transitive A R -> acyclic R.
Proof.
  eby repeat red; ins; eapply H, clos_trans_of_transitive. 
Qed.

Lemma restr_rel_trans :
  forall X dom rel, transitive X rel -> transitive X (restr_rel dom rel).
Proof.
  unfold restr_rel; red; ins; desf; eauto.
Qed.

Lemma clos_trans_of_clos_trans1 :
  forall X rel1 rel2 x y,
    clos_trans X (fun a b => clos_trans _ rel1 a b \/ rel2 a b) x y <->
    clos_trans X (fun a b => rel1 a b \/ rel2 a b) x y.
Proof.
  split; induction 1; desf; 
  eauto using clos_trans, clos_trans_mon.
Qed.

Lemma upward_clos_trans:
  forall X (rel: X -> X -> Prop) P,
    upward_closed rel P -> upward_closed (clos_trans _ rel) P.
Proof.
  ins; induction 1; by eauto.
Qed.

Lemma max_elt_clos_trans:
  forall X rel a b
         (hmax: max_elt rel a)
         (hclos: clos_trans X rel a b),
    False.
Proof.
  ins. eapply clos_trans_t1n in hclos. induction hclos; eauto.
Qed.

Lemma is_total_restr :
  forall X (dom : X -> Prop) rel,
    is_total dom rel ->
    is_total dom (restr_rel dom rel).
Proof.
  red; ins; eapply H in NEQ; eauto; desf; vauto.
Qed.

Lemma clos_trans_restrD :
  forall X rel f x y, clos_trans X (restr_rel f rel) x y -> f x /\ f y.
Proof.
  unfold restr_rel; induction 1; ins; desf. 
Qed.

Lemma clos_trans_restr_eqD :
  forall A rel B (f: A -> B) x y, clos_trans _ (restr_eq_rel f rel) x y -> f x = f y.
Proof.
  unfold restr_eq_rel; induction 1; ins; desf; congruence. 
Qed.

Lemma irreflexive_inclusion:
  forall X (R1 R2: relation X),
  inclusion X R1 R2 ->
  irreflexive R2 ->
  irreflexive R1.
Proof.
  unfold irreflexive, inclusion.
  by eauto.
Qed.

Lemma clos_trans_inclusion:
  forall X (R: relation X),
  inclusion X R (clos_trans X R).
Proof.
  unfold inclusion. intros.
  by econstructor; eauto.
Qed.

Lemma clos_trans_inclusion_clos_refl_trans:
  forall X (R: relation X),
  inclusion X (clos_trans X R) (clos_refl_trans X R).
Proof.
  unfold inclusion. intros.
  induction H.
    by eauto using rt_step.
    by eauto using rt_trans.
Qed.

Lemma clos_trans_monotonic:
  forall X (R1 R2: relation X),
  inclusion X R1 R2 ->
  inclusion X (clos_trans X R1) (clos_trans X R2).
Proof.
  intros.
  intros x y hR1.
  eapply clos_t1n_trans.
  eapply clos_trans_t1n in hR1.
  induction hR1.
    by eauto using clos_t1n_trans, t1n_step.
    (* [t1n_trans] is masked by a notation for [clos_t1n_trans] *)
    by eauto using clos_t1n_trans, Relation_Operators.t1n_trans.
Qed.

(******************************************************************************)
(** Set up setoid rewriting *)
(******************************************************************************)

Require Import Setoid.

Lemma same_relation_refl: forall A, reflexive _ (same_relation A).
Proof. split; ins. Qed.

Lemma same_relation_sym: forall A, symmetric _ (same_relation A).
Proof. unfold same_relation; split; ins; desf. Qed.

Lemma same_relation_trans: forall A, transitive _ (same_relation A).
Proof. unfold same_relation; split; ins; desf; red; eauto. Qed.

Add Parametric Relation (X : Type) : (relation X) (same_relation X) 
 reflexivity proved by (@same_relation_refl X)
 symmetry proved by (@same_relation_sym X)
 transitivity proved by (@same_relation_trans X)
 as same_rel.

Add Parametric Morphism X : (@union X) with 
  signature (@same_relation X) ==> (@same_relation X) ==> (@same_relation X) as union_mor.
Proof.
  unfold same_relation, union; ins; desf; split; red; ins; desf; eauto.
Qed.

Add Parametric Morphism X P : (@restr_rel X P) with 
  signature (@same_relation X) ==> (@same_relation X) as restr_rel_mor.
Proof.
  unfold same_relation, restr_rel; ins; desf; split; red; ins; desf; eauto.
Qed.

Add Parametric Morphism X : (@clos_trans X) with 
  signature (@same_relation X) ==> (@same_relation X) as clos_trans_mor.
Proof.
  unfold same_relation; ins; desf; split; red; ins; desf; eauto using clos_trans_mon.
Qed.

Add Parametric Morphism X : (@clos_refl_trans X) with 
  signature (@same_relation X) ==> (@same_relation X) as clos_relf_trans_mor.
Proof.
  unfold same_relation; ins; desf; split; red; ins; desf; eauto using clos_refl_trans_mon.
Qed.

Add Parametric Morphism X : (@irreflexive X) with 
  signature (@same_relation X) ==> iff as irreflexive_mor.
Proof.
  unfold same_relation; ins; desf; split; red; ins; desf; eauto using clos_refl_trans_mon.
Qed.

Add Parametric Morphism X : (@acyclic X) with 
  signature (@same_relation X) ==> iff as acyclic_mor.
Proof.
  unfold acyclic; ins; rewrite H; reflexivity.
Qed.


Lemma same_relation_restr X (f : X -> Prop) rel rel' :
   (forall x (CONDx: f x) y (CONDy: f y), rel x y <-> rel' x y) ->
   (restr_rel f rel <--> restr_rel f rel').
Proof.
  unfold restr_rel; split; red; ins; desf; rewrite H in *; eauto.
Qed.

Lemma union_restr X f rel rel' :
  union X (restr_rel f rel) (restr_rel f rel')
  <--> restr_rel f (union _ rel rel').
Proof.
  split; unfold union, restr_rel, inclusion; ins; desf; eauto.
Qed.

Lemma clos_trans_restr X f rel (UC: upward_closed rel f) :
  clos_trans X (restr_rel f rel) 
  <--> restr_rel f (clos_trans _ rel).
Proof.
  split; unfold union, restr_rel, inclusion; ins; desf; eauto.
    split; [|by apply clos_trans_restrD in H].
    by eapply clos_trans_mon; eauto; unfold restr_rel; ins; desf.
  clear H0; apply clos_trans_tn1 in H.
  induction H; eauto 10 using clos_trans.
Qed.


(******************************************************************************)
(** ** Lemmas about cycles *)
(******************************************************************************)

Lemma path_decomp_u1 X (rel : relation X) a b c d : 
  clos_trans X (rel UNION1 (a, b)) c d ->
  clos_trans X rel c d \/ 
  clos_refl_trans X rel c a /\ clos_refl_trans X rel b d.
Proof.
  induction 1; desf; eauto using clos_trans, clos_refl_trans, clos_trans_in_rt.
Qed.

Lemma cycle_decomp_u1 X (rel : relation X) a b c : 
  clos_trans X (rel UNION1 (a, b)) c c ->
  clos_trans X rel c c \/ clos_refl_trans X rel b a.
Proof.
  ins; apply path_decomp_u1 in H; desf; eauto using clos_refl_trans.
Qed.

Lemma path_decomp_u_total :
  forall X rel1 dom rel2 (T: is_total dom rel2) 
    (D: forall a b (REL: rel2 a b), dom a /\ dom b) x y
    (C: clos_trans X (fun a b => rel1 a b \/ rel2 a b) x y),
    clos_trans X rel1 x y \/
    (exists m n, 
      clos_refl_trans X rel1 x m /\ clos_trans X rel2 m n /\ clos_refl_trans X rel1 n y) \/
    (exists m n, 
      clos_refl_trans X rel1 m n /\ clos_trans X rel2 n m).
Proof.
  ins; induction C; desf; eauto 8 using rt_refl, clos_trans.
  by right; left; exists m, n; eauto using clos_trans_in_rt, rt_trans.
  by right; left; exists m, n; eauto using clos_trans_in_rt, rt_trans.

  destruct (classic (m = n0)) as [|NEQ]; desf.
  by right; left; exists m0, n; eauto using t_trans, rt_trans.
  eapply T in NEQ; desf.
    by right; right; exists n0, m; eauto 8 using clos_trans, rt_trans.
    by right; left; exists m0, n; eauto 8 using clos_trans, rt_trans.
    by apply t_step_rt in IHC0; desf; eapply D in IHC0; desf.
    by apply t_rt_step in IHC4; desf; eapply D in IHC6; desf.
Qed.

Lemma cycle_decomp_u_total :
  forall X rel1 dom rel2 (T: is_total dom rel2) 
    (D: forall a b (REL: rel2 a b), dom a /\ dom b) x
    (C: clos_trans X (fun a b => rel1 a b \/ rel2 a b) x x),
    clos_trans X rel1 x x \/
    (exists m n, clos_refl_trans X rel1 m n /\ clos_trans X rel2 n m).
Proof.
  ins; exploit path_decomp_u_total; eauto; ins; desf; eauto 8 using rt_trans.
Qed.

Lemma clos_trans_disj_rel :
  forall X (rel rel' : relation X)
    (DISJ: forall x y (R: rel x y) z (R': rel' y z), False) x y
    (R: clos_trans _ rel x y) z
    (R': clos_trans _ rel' y z),
    False.
Proof.
  ins; induction R; eauto; induction R'; eauto.
Qed.

Lemma path_decomp_u_1 :
  forall X (rel rel' : relation X)
    (DISJ: forall x y (R: rel x y) z (R': rel' y z), False) x y
    (T: clos_trans X (union X rel rel') x y),
    clos_trans _ rel x y \/ clos_trans _ rel' x y
    \/ exists z, clos_trans _ rel' x z /\ clos_trans _ rel z y.
Proof.
  unfold union; ins.
 induction T; desf; eauto 6 using clos_trans;
   try by exfalso; eauto using clos_trans_disj_rel.
Qed.

Lemma cycle_decomp_u_1 :
  forall X (rel rel' : relation X)
    (DISJ: forall x y (R: rel x y) z (R': rel' y z), False) x
    (T: clos_trans X (union X rel rel') x x),
    clos_trans _ rel x x \/ clos_trans _ rel' x x. 
Proof.
  ins; exploit path_decomp_u_1; eauto; ins; desf; eauto.
  exfalso; eauto using clos_trans_disj_rel.
Qed.

Lemma cycle_disj :
  forall X (rel : relation X)
    (DISJ: forall x y (R: rel x y) z (R': rel y z), False) x
    (T: clos_trans X rel x x), False.
Proof.
  ins; inv T; eauto using clos_trans_disj_rel.
Qed.

Lemma clos_trans_restr_trans_mid : 
  forall X (rel rel' : relation X) f x y
    (A : clos_trans _ (restr_rel f (fun x y => rel x y \/ rel' x y)) x y)
    z (B : rel y z) w
    (C : clos_trans _ (restr_rel f (fun x y => rel x y \/ rel' x y)) z w),
    clos_trans _ (restr_rel f (fun x y => rel x y \/ rel' x y)) x w.
Proof.
  ins; eapply t_trans, t_trans; vauto.
  eapply t_step; repeat split; eauto.
    by apply clos_trans_restrD in A; desc.
  by apply clos_trans_restrD in C; desc.
Qed.

Lemma clos_trans_restr_trans_cycle : 
  forall X (rel rel' : relation X) f x y
    (A : clos_trans _ (restr_rel f (fun x y => rel x y \/ rel' x y)) x y)
    (B : rel y x),
    clos_trans _ (restr_rel f (fun x y => rel x y \/ rel' x y)) x x.
Proof.
  ins; eapply t_trans, t_step; eauto. 
  by red; apply clos_trans_restrD in A; desf; auto.
Qed.


Lemma restr_eq_union : 
  forall X (rel rel' : relation X) B (f: X -> B) x y
         (R: forall x y, rel' x y -> f x = f y),
   restr_eq_rel f (fun x y => rel x y \/ rel' x y) x y <->
   restr_eq_rel f rel x y \/ rel' x y.
Proof.
  unfold restr_eq_rel; ins; intuition.
Qed.

Lemma clos_trans_restr_eq_union : 
  forall X (rel rel' : relation X) B (f: X -> B)
         (R: forall x y, rel' x y -> f x = f y),
   clos_trans _ (restr_eq_rel f (fun x y => rel x y \/ rel' x y)) <-->
   clos_trans _ (fun x y => restr_eq_rel f rel x y \/ rel' x y).
Proof.
  split; red; ins; eapply clos_trans_mon; eauto; ins; instantiate;
  rewrite restr_eq_union in *; eauto.
Qed.

Lemma acyclic_mon X (rel rel' : relation X) :
  acyclic rel -> inclusion _ rel' rel -> acyclic rel'.
Proof.
  eby repeat red; ins; eapply H, clos_trans_mon.
Qed. 

(** Extension of a partial order to a total order *)

Section one_extension.

  Variable X : Type.
  Variable elem : X.
  Variable rel : relation X.

  Definition one_ext : relation X := 
    fun x y =>
      clos_trans _ rel x y 
      \/ clos_refl_trans _ rel x elem /\ ~ clos_refl_trans _ rel y elem.

  Lemma one_ext_extends x y : rel x y -> one_ext x y. 
  Proof. vauto. Qed.

  Lemma one_ext_trans : transitive _ one_ext.
  Proof. 
    red; ins; unfold one_ext in *; desf; desf; 
      intuition eauto using clos_trans_in_rt, t_trans, rt_trans.
  Qed.
 
  Lemma one_ext_irr : acyclic rel -> irreflexive one_ext.
  Proof.
    red; ins; unfold one_ext in *; desf; eauto using clos_trans_in_rt.
  Qed.

  Lemma one_ext_total_elem : 
    forall x, x <> elem -> one_ext elem x \/ one_ext x elem.
  Proof.
    unfold one_ext; ins; rewrite !clos_refl_transE; tauto.
  Qed.

End one_extension.

Fixpoint tot_ext X (dom : list X) (rel : relation X) : relation X :=
  match dom with 
    | nil => clos_trans _ rel
    | x::l => one_ext x (tot_ext l rel) 
  end.

Lemma tot_ext_extends : 
  forall X dom (rel : relation X) x y, rel x y -> tot_ext dom rel x y. 
Proof. 
  induction dom; ins; eauto using t_step, one_ext_extends.
Qed.

Lemma tot_ext_trans : forall X dom rel, transitive X (tot_ext dom rel).
Proof. 
  induction dom; ins; vauto; apply one_ext_trans. 
Qed.

Lemma tot_ext_irr : 
  forall X (dom : list X) rel, acyclic rel -> irreflexive (tot_ext dom rel).
Proof.
  induction dom; ins.
  apply one_ext_irr, trans_irr_acyclic; eauto using tot_ext_trans.
Qed.

(*Lemma tot_ext_total : 
  forall X (dom : list X) rel, is_total (fun x => In x dom) (tot_ext dom rel).
Proof.
  induction dom; red; ins; desf.
  eapply one_ext_total_elem in NEQ; desf; eauto.
  eapply nesym, one_ext_total_elem in NEQ; desf; eauto.
  eapply IHdom in NEQ; desf; eauto using one_ext_extends.
Qed.*)

Lemma tot_ext_inv :
  forall X dom rel (x y : X),
    acyclic rel -> tot_ext dom rel x y -> ~ rel y x.
Proof.
  red; ins; eapply tot_ext_irr, tot_ext_trans, tot_ext_extends; eauto.
Qed.


(** Misc properties *)
(******************************************************************************)


Lemma clos_trans_imm :
  forall X (R : relation X) (I: irreflexive R) 
         (T: transitive _ R) L (ND: NoDup L) a b
         (D: forall c, R a c -> R c b -> In c L)
         (REL: R a b),
    clos_trans _ (immediate R) a b.
Proof.
  intros until 3; induction ND; ins; vauto.
  destruct (classic (R a x /\ R x b)) as [|N]; desf;
    [apply t_trans with x|]; eapply IHND; ins;
    exploit (D c); eauto; intro; desf; exfalso; eauto.
Qed.


(** Remove duplicate list elements (classical) *)
(******************************************************************************)

Require Import extralib.

Fixpoint undup A dec (l: list A) :=
  match l with nil => nil
    | x :: l =>
      if In_dec dec x l then undup dec l else x :: undup dec l
  end.

Lemma In_undup X dec (x: X) l : In x (undup dec l) <-> In x l.
Proof.
  induction l; ins; des_if; ins; rewrite IHl; split; ins; desf; vauto.
Qed.

Lemma NoDup_undup X dec (l : list X) : NoDup (undup dec l).
Proof.
  induction l; ins; desf; constructor; eauto; rewrite In_undup; eauto. 
Qed.


Lemma clos_trans_imm2 :
  forall X (dec : forall x y : X, {x = y} + {x <> y}) 
         (R : relation X) (I: irreflexive R) 
         (T: transitive _ R) L a b
         (D: forall c, R a c -> R c b -> In c L)
         (REL: R a b),
    clos_trans _ (immediate R) a b.
Proof.
  ins; eapply clos_trans_imm with (L := undup dec L); ins;
  try rewrite In_undup; eauto using NoDup_undup.
Qed.




Lemma total_immediate_unique:
  forall X (eq_X_dec: forall (x y: X), {x=y} + {x<>y}) (rel: X -> X -> Prop) (P: X -> Prop)
         (Tot: is_total P rel)
         a b c (pa: P a) (pb: P b) (pc: P c)
         (iac: immediate rel a c)
         (ibc: immediate rel b c),
    a = b.
Proof.
  ins.
  destruct (eq_X_dec a b); eauto.
  exfalso.
  unfold immediate in *; desf.
  eapply Tot in n; eauto.
  desf; eauto.
Qed.

