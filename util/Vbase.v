
(* *********************************************************************)
(*                                                                     *)
(*                      Basic lemmas & tactics                         *)
(*                                                                     *)
(* *********************************************************************)

(** This file collects a number of basic lemmas and tactics for better
    proof automation, structuring large proofs, or rewriting.  Most of 
    the rewriting support is ported from ss-reflect. *)

(** Symbols starting with [vlib__] are internal. *)

Require Import Logic.Eqdep.
Require Import Bool.
Require Import Arith.
Require Import ZArith.
Require Import String.

Open Scope bool_scope.
Open Scope list_scope.

Set Implicit Arguments.
Unset Strict Implicit.

(* ************************************************************************** *)
(** * Axioms *)
(* ************************************************************************** *)

Require ClassicalFacts.
Require Export FunctionalExtensionality.
Require Export ProofIrrelevance.

Ltac exten := apply functional_extensionality.

(* ************************************************************************** *)
(** * Coersion of [bool] into [Prop] *)
(* ************************************************************************** *)

(** Coersion of bools into Prop *)
Coercion is_true (b : bool) : Prop := b = true.

(** Hints for auto *)
Lemma vlib__true_is_true : true.
Proof. reflexivity. Qed.

Lemma vlib__not_false_is_true : ~ false.
Proof. discriminate. Qed.

Hint Resolve vlib__true_is_true vlib__not_false_is_true.

(* ************************************************************************** *)
(** * Very basic automation *)
(* ************************************************************************** *)

(** Set up for basic simplification *)

Create HintDb vlib discriminated. 

(** Adaptation of the ss-reflect "[done]" tactic. *)

Ltac vlib__basic_done := 
  solve [trivial with vlib | apply sym_equal; trivial | discriminate | contradiction].

Ltac done := trivial with vlib; hnf; intros;
  solve [try vlib__basic_done; split; 
         try vlib__basic_done; split; 
         try vlib__basic_done; split; 
         try vlib__basic_done; split; 
         try vlib__basic_done; split; vlib__basic_done
    | match goal with H : ~ _ |- _ => solve [case H; trivial] end].

(** A variant of the ssr "done" tactic that performs "eassumption". *)

Ltac edone := try eassumption; trivial; hnf; intros;
  solve [try eassumption; try vlib__basic_done; split; 
         try eassumption; try vlib__basic_done; split; 
         try eassumption; try vlib__basic_done; split; 
         try eassumption; try vlib__basic_done; split; 
         try eassumption; try vlib__basic_done; split;
         try eassumption; vlib__basic_done
    | match goal with H : ~ _ |- _ => solve [case H; trivial] end].

Tactic Notation "by"  tactic(tac) := (tac; done).
Tactic Notation "eby" tactic(tac) := (tac; edone).


(* ************************************************************************** *)
(** * Boolean reflection *)
(* ************************************************************************** *)

(** These definitions are ported from ssr-bool. *)

(** Negation lemmas *)
Section NegationLemmas.

  Variables (b c : bool).

  Lemma negbT : b = false -> negb b.
  Proof. by case b. Qed.
  Lemma negbTE: negb b -> b = false.
  Proof. by case b. Qed.
  Lemma negbF : b -> negb b = false.
  Proof. by case b. Qed.
  Lemma negbFE: negb b = false -> b.
  Proof. by case b. Qed.
  Lemma negbNE: negb (negb b) -> b.
  Proof. by case b. Qed.

  Lemma negbLR : b = negb c -> negb b = c.
  Proof. by case c; intro X; rewrite X. Qed.

  Lemma negbRL : negb b = c -> b = negb c.
  Proof. by case b; intro X; rewrite <- X. Qed.

  Lemma contra : (c -> b) -> negb b -> negb c.
  Proof. by case b; case c. Qed.

End NegationLemmas.

(** Lemmas for ifs, which allow reasoning about the condition without 
    repeating it inside the proof. *)
Section BoolIf.

Variables (A B : Type) (x : A) (f : A -> B) (b : bool) (vT vF : A).

Inductive if_spec : A -> bool -> Set :=
  | IfSpecTrue  : b         -> if_spec vT true
  | IfSpecFalse : b = false -> if_spec vF false.

Lemma ifP : if_spec (if b then vT else vF) b.
Proof. by case_eq b; constructor. Qed.

Lemma if_same : (if b then vT else vT) = vT.
Proof. by case b. Qed.

Lemma if_neg : (if negb b then vT else vF) = if b then vF else vT.
Proof. by case b. Qed.

Lemma fun_if : f (if b then vT else vF) = if b then f vT else f vF.
Proof. by case b. Qed.

Lemma if_arg : forall fT fF : A -> B,
  (if b then fT else fF) x = if b then fT x else fF x.
Proof. by case b. Qed.

End BoolIf.

(** The reflection predicate *)
Inductive reflect (P : Prop) : bool -> Set :=
  | ReflectT : P -> reflect P true
  | ReflectF : ~ P -> reflect P false.

(** Internal reflection lemmas *)
Section ReflectCore.

Variables (P : Prop) (b : bool) (Hb : reflect P b) (Q : Prop) (c : bool).

Lemma introNTF : (if c then ~ P else P) -> negb b = c.
Proof. by case c; case Hb. Qed.

Lemma introTF : (if c then P else ~ P) -> b = c.
Proof. by case c; case Hb. Qed.

Lemma elimNTF : negb b = c -> if c then ~ P else P.
Proof. by intro X; rewrite <- X; case Hb. Qed.

Lemma elimTF : b = c -> if c then P else ~ P.
Proof. by intro X; rewrite <- X; case Hb. Qed.

Lemma equivPif : (Q -> P) -> (P -> Q) -> if b then Q else ~ Q.
Proof. by case Hb; auto. Qed.

Lemma xorPif : Q \/ P -> ~ (Q /\ P) -> if b then ~ Q else Q.
Proof. by case Hb; [intros ? _ H ? | intros ? H _]; case H. Qed.

End ReflectCore.

(** Internal negated reflection lemmas *)
Section ReflectNegCore.

Variables (P : Prop) (b : bool) (Hb : reflect P (negb b)) (Q : Prop) (c : bool).

Lemma introTFn : (if c then ~ P else P) -> b = c.
Proof. by intro X; apply (introNTF Hb) in X; rewrite <- X; case b. Qed.

Lemma elimTFn : b = c -> if c then ~ P else P.
Proof. by intro X; rewrite <- X; apply (elimNTF Hb); case b. Qed.

Lemma equivPifn : (Q -> P) -> (P -> Q) -> if b then ~ Q else Q.
Proof. by rewrite <- if_neg; apply equivPif. Qed.

Lemma xorPifn : Q \/ P -> ~ (Q /\ P) -> if b then Q else ~ Q.
Proof. by rewrite <- if_neg; apply xorPif. Qed.

End ReflectNegCore.

(** User-oriented reflection lemmas *)
Section Reflect.

Variables (P Q : Prop) (b b' c : bool).
Hypotheses (Pb : reflect P b) (Pb' : reflect P (negb b')).

Lemma introT  : P -> b.
Proof. by apply (introTF Pb (c:=true)). Qed.
Lemma introF  : ~ P -> b = false.
Proof. by apply (introTF Pb (c:=false)). Qed.
Lemma introN  : ~ P -> negb b.
Proof. by apply (introNTF Pb (c:=true)). Qed.
Lemma introNf : P -> negb b = false.
Proof. by apply (introNTF Pb (c:=false)). Qed.
Lemma introTn : ~ P -> b'.
Proof. by apply (introTFn Pb' (c:=true)). Qed.
Lemma introFn : P -> b' = false.
Proof. by apply (introTFn Pb' (c:=false)). Qed.

Lemma elimT  : b -> P.
Proof. by apply (@elimTF _ _ Pb true). Qed.
Lemma elimF  : b = false -> ~ P.
Proof. by apply (@elimTF  _ _ Pb false). Qed.
Lemma elimN  : negb b -> ~P.
Proof. by apply (@elimNTF _ _ Pb true). Qed.
Lemma elimNf : negb b = false -> P.
Proof. by apply (@elimNTF _ _ Pb false). Qed.
Lemma elimTn : b' -> ~ P.
Proof. by apply (@elimTFn _ _ Pb' true). Qed.
Lemma elimFn : b' = false -> P.
Proof. by apply (@elimTFn _ _ Pb' false). Qed.

Lemma introP : (b -> Q) -> (negb b -> ~ Q) -> reflect Q b.
Proof. by case b; constructor; auto. Qed.

Lemma iffP : (P -> Q) -> (Q -> P) -> reflect Q b.
Proof. by case Pb; constructor; auto. Qed.

Lemma appP : reflect Q b -> P -> Q.
Proof. by intro Qb; intro X; apply introT in X; revert X; case Qb. Qed.

Lemma sameP : reflect P c -> b = c.
Proof. intro X; case X; [exact introT | exact introF]. Qed.

Lemma decPcases : if b then P else ~ P.
Proof. by case Pb. Qed.

Definition decP : {P} + {~ P}.
Proof. by generalize decPcases; case b; [left | right]. Defined.

End Reflect.

(* Allow the direct application of a reflection lemma to a boolean assertion.  *)
Coercion elimT : reflect >-> Funclass.

Section ReflectConnectives.

Variable b1 b2 b3 b4 b5 : bool.

Lemma idP : reflect b1 b1.
Proof. by case b1; constructor. Qed.

Lemma idPn : reflect (negb b1) (negb b1).
Proof. by case b1; constructor. Qed.

Lemma negP : reflect (~ b1) (negb b1).
Proof. by case b1; constructor; auto. Qed.

Lemma negPn : reflect b1 (negb (negb b1)).
Proof. by case b1; constructor. Qed.

Lemma negPf : reflect (b1 = false) (negb b1).
Proof. by case b1; constructor. Qed.

Lemma andP : reflect (b1 /\ b2) (b1 && b2).
Proof. by case b1; case b2; constructor; try done; intro X; case X. Qed.

Lemma orP : reflect (b1 \/ b2) (b1 || b2).
Proof. by case b1; case b2; constructor; auto; intro X; case X. Qed.

Lemma nandP : reflect (negb b1 \/ negb b2) (negb (b1 && b2)).
Proof. by case b1; case b2; constructor; auto; intro X; case X; auto. Qed.

Lemma norP : reflect (negb b1 /\ negb b2) (negb (b1 || b2)).
Proof. by case b1; case b2; constructor; auto; intro X; case X; auto. Qed.

End ReflectConnectives.

(* ************************************************************************** *)
(** * Equality types *)
(* ************************************************************************** *)

(** These definitions are ported from ssr-eq. *)

Inductive phantom (T :  Type) (p : T) :  Type := Phantom.
Implicit Arguments phantom [].
Implicit Arguments Phantom [].
Definition phant_id T1 T2 v1 v2 := phantom T1 v1 -> phantom T2 v2.
Definition idfun T := (fun x : T => x).

Module Equality.

Definition axiom T (e : T -> T -> bool) := forall x y, reflect (x = y) (e x y).

Structure mixin_of T := Mixin {op : T -> T -> bool; _ : axiom op}.
Notation class_of := mixin_of (only parsing).

Section ClassDef.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class cT' := match cT' return class_of cT' with Pack _ c _ => c end.

Definition pack c := @Pack T c T.
Definition clone := fun c (_ : cT -> T) (_ : phant_id (pack c) cT) => pack c.

End ClassDef.

Module Exports.
Coercion sort : type >-> Sortclass.
Notation eqType := type.
Notation EqMixin := Mixin.
Notation EqType T m := (@pack T m).
Notation "[ 'eqMixin' 'of' T ]" := (class _ : mixin_of T)
  (at level 0, format "[ 'eqMixin'  'of'  T ]") : form_scope.
Notation "[ 'eqType' 'of' T 'for' C ]" := (@clone T C _ idfun id)
  (at level 0, format "[ 'eqType'  'of'  T  'for'  C ]") : form_scope.
Notation "[ 'eqType' 'of' T ]" := (@clone T _ _ id id)
  (at level 0, format "[ 'eqType'  'of'  T ]") : form_scope.
End Exports.

End Equality.
Export Equality.Exports.

Definition eq_op T := Equality.op (Equality.class T).
Implicit Arguments eq_op [[T]].

Lemma eqE : forall T x, eq_op x = Equality.op (Equality.class T) x.
Proof. done. Qed.

Lemma eqP : forall T, Equality.axiom (@eq_op T).
Proof. by unfold eq_op; destruct T as (? & []). Qed.
Implicit Arguments eqP [T].

Notation "x == y" := (eq_op x y)
  (at level 70, no associativity) : bool_scope.
Notation "x == y :> T" := ((x : T) == (y : T))
  (at level 70, y at next level) : bool_scope.
Notation "x != y" := (negb (x == y))
  (at level 70, no associativity) : bool_scope.
Notation "x != y :> T" := (negb (x == y :> T))
  (at level 70, y at next level) : bool_scope.

Lemma vlib__internal_eqP : 
  forall (T: eqType) (x y : T), reflect (x = y) (x == y).
Proof. apply eqP. Qed.

Lemma neqP : forall (T: eqType) (x y: T), reflect (x <> y) (x != y).
Proof. intros; case eqP; constructor; auto. Qed.

Lemma beq_refl : forall (T : eqType) (x : T), x == x.
Proof. by intros; case eqP. Qed.

Lemma beq_sym : forall (T : eqType) (x y : T), (x == y) = (y == x).
Proof. intros; do 2 case eqP; congruence. Qed.

Hint Resolve beq_refl : vlib.
Hint Rewrite beq_refl : vlib_trivial.

Notation eqxx := beq_refl.


(*
Implicit Arguments idP [b1].
Implicit Arguments idPn [b1].
Implicit Arguments negP [b1].
Implicit Arguments negn [b1].
Implicit Arguments negPf [b1].
Implicit Arguments andP [b1 b2].
Implicit Arguments orP [b1 b2].
Implicit Arguments nandP [b1 b2].
Implicit Arguments norP [b1 b2].
*)

(* ************************************************************************** *)
(** * Basic simplification tactics *)
(* ************************************************************************** *)


Lemma vlib__negb_rewrite : forall b, negb b -> b = false.
Proof. by intros []. Qed.

Lemma vlib__andb_split : forall b1 b2, b1 && b2 -> b1 /\ b2.
Proof. by intros [] []. Qed.

Lemma vlib__nandb_split : forall b1 b2, b1 && b2 = false -> b1 = false \/ b2 = false.
Proof. intros [] []; auto. Qed. 

Lemma vlib__orb_split : forall b1 b2, b1 || b2 -> b1 \/ b2.
Proof. intros [] []; auto. Qed.

Lemma vlib__norb_split : forall b1 b2, b1 || b2 = false -> b1 = false /\ b2 = false.
Proof. intros [] []; auto. Qed.

Lemma vlib__eqb_split : forall b1 b2 : bool, (b1 -> b2) -> (b2 -> b1) -> b1 = b2.
Proof. intros [] [] H H'; unfold is_true in *; auto using sym_eq. Qed.

Lemma vlib__beq_rewrite : forall (T : eqType) (x1 x2 : T), x1 == x2 -> x1 = x2.
Proof. by intros until 0; case eqP. Qed.


(** Set up for basic simplification: database of reflection lemmas *)

Create HintDb vlib_refl discriminated.  

Hint Resolve andP orP nandP norP negP vlib__internal_eqP neqP : vlib_refl.

Ltac vlib__complaining_inj f H :=
  let X := fresh in
  (match goal with | [|- ?P ] => set (X := P) end);
  injection H;
  (*  (lazymatch goal with | [ |- f _ = f _ -> _] => fail | _ => idtac end);  
      (* Previous statement no longer necessary in 8.4 *) *)
  clear H; intros; subst X;
  try subst.

Ltac vlib__clarify1 :=
  try subst;
  repeat match goal with
  | [H: is_true (andb _ _) |- _] => 
      let H' := fresh H in case (vlib__andb_split H); clear H; intros H' H
  | [H: is_true (negb ?x) |- _] => rewrite (vlib__negb_rewrite H) in *
  | [H: is_true ?x        |- _] => rewrite H in *
  | [H: ?x = true         |- _] => rewrite H in *
  | [H: ?x = false        |- _] => rewrite H in *
  | [H: is_true (_ == _)  |- _] => generalize (vlib__beq_rewrite H); clear H; intro H
  | [H: @existT _ _ _ _ = @existT _ _ _ _ |- _] => apply inj_pair2 in H; try subst
  | [H: ?f _             = ?f _             |- _] => vlib__complaining_inj f H
  | [H: ?f _ _           = ?f _ _           |- _] => vlib__complaining_inj f H
  | [H: ?f _ _ _         = ?f _ _ _         |- _] => vlib__complaining_inj f H
  | [H: ?f _ _ _ _       = ?f _ _ _ _       |- _] => vlib__complaining_inj f H
  | [H: ?f _ _ _ _ _     = ?f _ _ _ _ _     |- _] => vlib__complaining_inj f H
  | [H: ?f _ _ _ _ _ _   = ?f _ _ _ _ _ _   |- _] => vlib__complaining_inj f H
  | [H: ?f _ _ _ _ _ _ _ = ?f _ _ _ _ _ _ _ |- _] => vlib__complaining_inj f H
  end; try done.

(** Perform injections & discriminations on all hypotheses *)

Ltac clarify :=
  vlib__clarify1;
  repeat match goal with
    | H1: ?x = Some _, H2: ?x = None   |- _ => rewrite H2 in H1; discriminate
    | H1: ?x = Some _, H2: ?x = Some _ |- _ => rewrite H2 in H1; vlib__clarify1
  end; (* autorewrite with vlib_trivial; *) try done.

(** Kill simple goals that require up to two econstructor calls. *)

Ltac vauto :=
  (clarify; try edone; 
   try (econstructor (solve [edone | econstructor (edone) ]))).

(** Check that the hypothesis [id] is defined. This is useful to make sure that
    an [assert] has been completely finished. *)
    
Ltac end_assert id := 
  let m := fresh in 
  pose (m := refl_equal id); clear m.

Ltac inv x := inversion x; clarify.
Ltac simpls  := simpl in *; try done.
Ltac ins := simpl in *; try done; intros.

Tactic Notation "case_eq" constr(x) := case_eq (x).

Tactic Notation "case_eq" constr(x) "as" simple_intropattern(H) :=
  destruct x as [] _eqn: H; try done.

Ltac vlib__clarsimp1 :=
  clarify; (autorewrite with vlib_trivial vlib in * ); 
  (autorewrite with vlib_trivial in * ); try done;
  clarify; auto 1 with vlib.

Ltac clarsimp := intros; simpl in *; vlib__clarsimp1.

Ltac autos   := clarsimp; auto with vlib.


(* ************************************************************************** *)
(** Destruct but give useful names *)
(* ************************************************************************** *)

Definition NW A (P: unit -> A) : A := P tt.

(*Notation "<< x : t >>" := (NW (fun x => t)) (at level 80, x ident, no associativity).
Notation "<< t >>" := (NW (fun _ => t)) (at level 79, no associativity).*)

Ltac unnw := unfold NW in *.
Ltac rednw := red; unnw.

Hint Unfold NW.

(** Destruct, but no case split *)
Ltac desc :=
  repeat match goal with
    | H: is_true (_ == _) |- _ => generalize (vlib__beq_rewrite H); clear H; intro H
    | H : exists x, NW (fun y => _) |- _ =>
      let x' := fresh x in let y' := fresh y in destruct H as [x' y']; red in y'
    | H : exists x, ?p |- _ =>
      let x' := fresh x in destruct H as [x' H]
    | H : ?p /\ ?q |- _ =>
      let x' := match p with | NW (fun z => _) => fresh z | _ => H end in
      let y' := match q with | NW (fun z => _) => fresh z | _ => fresh H end in
      destruct H as [x' y'];
      match p with | NW _ => red in x' | _ => idtac end;
      match q with | NW _ => red in y' | _ => idtac end
    | H : is_true (_ && _) |- _ => 
          let H' := fresh H in case (vlib__andb_split H); clear H; intros H H'
    | H : (_ || _) = false |- _ =>
          let H' := fresh H in case (vlib__norb_split H); clear H; intros H H'
    | H : ?x = ?x   |- _ => clear H

(*    | H: is_true ?x |- _ => eapply elimT in H; [|solve [trivial with vlib_refl]]
    | H: ?x = true  |- _ => eapply elimT in H; [|solve [trivial with vlib_refl]]
    | H: ?x = false |- _ => eapply elimFn in H; [|solve [trivial with vlib_refl]]
    | H: ?x = false |- _ => eapply elimF in H; [|solve [trivial with vlib_refl]]  *)
  end.

Ltac des :=
  repeat match goal with
    | H: is_true (_ == _) |- _ => generalize (vlib__beq_rewrite H); clear H; intro H
    | H : exists x, NW (fun y => _) |- _ =>
      let x' := fresh x in let y' := fresh y in destruct H as [x' y']; red in y'
    | H : exists x, ?p |- _ =>
      let x' := fresh x in destruct H as [x' H]
    | H : exists2 x, ?p & ?q |- _ =>
      let x' := fresh x in destruct H as [x' H1 H2]
    | H : ?p /\ ?q |- _ =>
      let x' := match p with | NW (fun z => _) => fresh z | _ => H end in
      let y' := match q with | NW (fun z => _) => fresh z | _ => fresh H end in
      destruct H as [x' y'];
      match p with | NW _ => red in x' | _ => idtac end;
      match q with | NW _ => red in y' | _ => idtac end
    | H : is_true (_ && _) |- _ => 
        let H' := fresh H in case (vlib__andb_split H); clear H; intros H H'
    | H : (_ || _) = false |- _ =>
        let H' := fresh H in case (vlib__norb_split H); clear H; intros H H'
    | H : ?x = ?x |- _ => clear H
(*    | H: is_true ?x |- _ => eapply elimT in H; [|solve [trivial with vlib_refl]]
    | H: ?x = true  |- _ => eapply elimT in H; [|solve [trivial with vlib_refl]]
    | H: ?x = false |- _ => eapply elimFn in H; [|solve [trivial with vlib_refl]]
    | H: ?x = false |- _ => eapply elimF in H; [|solve [trivial with vlib_refl]] *)
    | H : ?p <-> ?q |- _ =>
      let x' := match p with | NW (fun z => _) => fresh z | _ => H end in
      let y' := match q with | NW (fun z => _) => fresh z | _ => fresh H end in
      destruct H as [x' y'];
      match p with | NW _ => unfold NW at 1 in x'; red in y' | _ => idtac end;
      match q with | NW _ => unfold NW at 1 in y'; red in x' | _ => idtac end
    | H : ?p \/ ?q |- _ =>
      let x' := match p with | NW (fun z => _) => fresh z | _ => H end in
      let y' := match q with | NW (fun z => _) => fresh z | _ => H end in
      destruct H as [x' | y'];
      [ match p with | NW _ => red in x' | _ => idtac end
      | match q with | NW _ => red in y' | _ => idtac end]
    | H : is_true (_ || _) |- _ => case (vlib__orb_split H); clear H; intro H
    | H : (_ && _) = false |- _ => case (vlib__nandb_split H); clear H; intro H
  end.

Ltac des_if_asm :=
  clarify;
  repeat 
    match goal with 
      | H: context[ match ?x with _ => _ end ] |- _ => 
        match (type of x) with
          | { _ } + { _ } => destruct x; clarify
          | bool => 
            let Heq := fresh "Heq" in
            let P := fresh in
            evar(P: Prop);
            assert (Heq: reflect P x) by (subst P; trivial with vlib_refl); 
            subst P; destruct Heq as [Heq|Heq]
          | _ => let Heq := fresh "Heq" in destruct x as [] _eqn: Heq; clarify
        end 
    end.

Ltac des_if_goal :=
  clarify;
  repeat 
    match goal with 
      | |- context[match ?x with _ => _ end] => 
        match (type of x) with
          | { _ } + { _ } => destruct x; clarify
          | bool => 
            let Heq := fresh "Heq" in
            let P := fresh in
            evar(P: Prop);
            assert (Heq: reflect P x) by (subst P; trivial with vlib_refl); 
            subst P; destruct Heq as [Heq|Heq]
          | _ => let Heq := fresh "Heq" in destruct x as [] _eqn: Heq; clarify
        end 
    end.

Ltac des_if :=
  clarify;
  repeat 
    match goal with 
      | |- context[match ?x with _ => _ end] => 
        match (type of x) with
          | { _ } + { _ } => destruct x; clarify
          | bool => 
            let Heq := fresh "Heq" in
            let P := fresh in
            evar(P: Prop);
            assert (Heq: reflect P x) by (subst P; trivial with vlib_refl); 
            subst P; destruct Heq as [Heq|Heq]
          | _ => let Heq := fresh "Heq" in destruct x as [] _eqn: Heq; clarify
        end 
      | H: context[ match ?x with _ => _ end ] |- _ => 
        match (type of x) with
          | { _ } + { _ } => destruct x; clarify
          | bool => 
            let Heq := fresh "Heq" in
            let P := fresh in
            evar(P: Prop);
            assert (Heq: reflect P x) by (subst P; trivial with vlib_refl); 
            subst P; destruct Heq as [Heq|Heq]
          | _ => let Heq := fresh "Heq" in destruct x as [] _eqn: Heq; clarify
        end 
    end.

Ltac des_eqrefl :=
  match goal with
    | H: context[match ?X as id return (id = ?X -> _) with _ => _ end Logic.eq_refl] |- _ =>
    let EQ := fresh "EQ" in
    let id' := fresh "x" in
    revert H;
    generalize (Logic.eq_refl X); generalize X at 1 3;
    intros id' EQ; destruct id'; intros H
    | |- context[match ?X as id return (id = ?X -> _) with _ => _ end Logic.eq_refl] =>
    let EQ := fresh "EQ" in
    let id' := fresh "x" in
    generalize (Logic.eq_refl X); generalize X at 1 3;
    intros id' EQ; destruct id'
  end.

Ltac desf_asm := clarify; des; des_if_asm.

Ltac desf := clarify; des; des_if.

Ltac clarassoc := clarsimp; autorewrite with vlib_trivial vlib vlibA in *; try done. 

Ltac vlib__hacksimp1 :=
   clarsimp;
   match goal with
     | H: _ |- _ => solve [rewrite H; clear H; clarsimp
                         |rewrite <- H; clear H; clarsimp]
     | _ => solve [f_equal; clarsimp]
   end.

Ltac hacksimp :=
   clarsimp;
   try match goal with
   | H: _ |- _ => solve [rewrite H; clear H; clarsimp
                              |rewrite <- H; clear H; clarsimp]
   | |- context[match ?p with _ => _ end] => solve [destruct p; vlib__hacksimp1]
   | _ => solve [f_equal; clarsimp]
   end.

(* ************************************************************************** *)
(** ** Delineating cases in proofs *)
(* ************************************************************************** *)

(** Named case tactics (taken from Libtactics) *)

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move x at top
  | assert_eq x name
  | fail 1 "because we are working on a different case." ].

Ltac Case name := Case_aux case name.
Ltac SCase name := Case_aux subcase name.
Ltac SSCase name := Case_aux subsubcase name.
Ltac SSSCase name := Case_aux subsubsubcase name.
Ltac SSSSCase name := Case_aux subsubsubsubcase name.

(** Lightweight case tactics (without names) *)

Tactic Notation "--" tactic(c) :=
  first [
    assert (WithinCaseM := True); move WithinCaseM at top
  | fail 1 "because we are working on a different case." ]; c.

Tactic Notation "++" tactic(c) :=
  first [
    assert (WithinCaseP := True); move WithinCaseP at top
  | fail 1 "because we are working on a different case." ]; c.

(* ************************************************************************** *)
(** ** Exploiting a hypothesis *)
(* ************************************************************************** *)

(** Exploit an assumption (adapted from CompCert). *)

Ltac exploit x :=
    refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _ _) _)
 || refine ((fun x y => y x) (x _ _ _) _)
 || refine ((fun x y => y x) (x _ _) _)
 || refine ((fun x y => y x) (x _) _).

(* http://comments.gmane.org/gmane.science.mathematics.logic.coq.club/7013 *)
Ltac feed H :=
  match type of H with
  | ?foo -> _ =>
    let FOO := fresh in
    assert foo as FOO; [|specialize (H FOO); clear FOO]
  end.

Ltac feed_n n H := match constr:n with
  | O => idtac
  | (S ?m) => feed H ; [| feed_n m H]
end.