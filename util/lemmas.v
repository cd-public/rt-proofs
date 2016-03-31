Add LoadPath ".." as rt.
Require Import rt.util.Vbase rt.util.divround rt.util.ssromega.
Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop tuple path div.

(* Here we define a more verbose notation for projections of pairs... *)
Section Pair.

  Context {A B: Type}.
  Variable p: A * B.
  Definition pair_1st := fst p.
  Definition pair_2nd := snd p.

End Pair.

(* ...and triples. *)
Section Triple.

  Context {A B C: Type}.
  Variable p: A * B * C.
  Definition triple_1st (p: A * B * C) := fst (fst p).
  Definition triple_2nd := snd (fst p).
  Definition triple_3rd := snd p.

End Triple.

(* Define a wrapper from an element to a singleton list. *)
Definition make_sequence {T: Type} (opt: option T) :=
  match opt with
    | Some j => [:: j]
    | None => [::]
  end.

(* Next we define a notation for the big concatenation operator.*)
  
Reserved Notation "\cat_ ( m <= i < n ) F"
  (at level 41, F at level 41, i, m, n at level 50,
   format "'[' \cat_ ( m <= i < n ) '/ ' F ']'").

Notation "\cat_ ( m <= i < n ) F" :=
  (\big[cat/[::]]_(m <= i < n) F%N) : nat_scope.

Reserved Notation "\cat_ ( m <= i < n | P ) F"
  (at level 41, F at level 41, P at level 41, i, m, n at level 50,
   format "'[' \cat_ ( m <= i < n | P ) '/ ' F ']'").

Notation "\cat_ ( m <= i < n | P ) F" :=
  (\big[cat/[::]]_(m <= i < n | P) F%N) : nat_scope.

Reserved Notation "\cat_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
   format "'[' \cat_ ( i < n ) '/ ' F ']'").

Notation "\cat_ ( i < n ) F" :=
  (\big[cat/[::]]_(i < n) F%N) : nat_scope.

Reserved Notation "\cat_ ( i < n | P ) F"
  (at level 41, F at level 41, i, n at level 50,
   format "'[' \cat_ ( i < n | P ) '/ ' F ']'").

Notation "\cat_ ( i < n | P ) F" :=
  (\big[cat/[::]]_(i < n | P) F%N) : nat_scope.
  
(* Let's define big operators for lists of pairs. *)

Reserved Notation "\sum_ ( ( m , n ) <- r ) F"
  (at level 41, F at level 41, m, n at level 50,
   format "'[' \sum_ ( ( m , n ) <- r ) '/ ' F ']'").

Notation "\sum_ ( ( m , n ) <- r ) F" :=
  (\sum_(i <- r) (let '(m,n) := i in F)) : nat_scope.

Reserved Notation "\sum_ ( ( m , n ) <- r | P ) F"
  (at level 41, F at level 30, P at level 41, m, n at level 50,
   format "'[' \sum_ ( ( m , n ) <- r | P ) '/ ' F ']'").

Notation "\sum_ ( ( m , n ) <- r | P ) F" :=
  (\sum_(i <- r | (let '(m,n) := i in P))
    (let '(m,n) := i in F)) : nat_scope.

Reserved Notation "\max_ ( ( m , n ) <- r ) F"
  (at level 41, F at level 41, m, n at level 50,
   format "'[' \max_ ( ( m , n ) <- r ) '/ ' F ']'").

Notation "\max_ ( ( m , n ) <- r ) F" :=
  (\max_(i <- r) (let '(m,n) := i in F)) : nat_scope.

Reserved Notation "\max_ ( ( m , n ) <- r | P ) F"
  (at level 41, F at level 30, P at level 41, m, n at level 50,
   format "'[' \max_ ( ( m , n ) <- r | P ) '/ ' F ']'").

Notation "\max_ ( ( m , n ) <- r | P ) F" :=
  (\max_(i <- r | (let '(m,n) := i in P))
    (let '(m,n) := i in F)) : nat_scope.

Notation "[ 'seq' ( x , y ) <- s | C ]" :=
  (filter (fun i => let '(x,y) := i in C%B) s)
 (at level 0, x at level 99,
  format "[ '[hv' 'seq' ( x , y ) <- s '/ ' | C ] ']'") : seq_scope.

(* In case we use an (option list T), we can define membership
   without having to match the option type. *)
Reserved Notation "x \In A"
  (at level 70, format "'[hv' x '/ ' \In A ']'", no associativity).
Notation "x \In A" :=
  (if A is Some B then in_mem x (mem B) else false) : bool_scope.

(* The following tactic does dependent pattern matching of
   a bool (in case we use the result of the bool as a proof term). *)
Ltac des_eqrefl2 :=
  match goal with
    | H: context[match ?X as id return (?X = id -> _) with _ => _ end Logic.eq_refl] |- _ =>
    let EQ := fresh "EQ" in
    let id' := fresh "x" in
    revert H;
    generalize (Logic.eq_refl X); generalize X at 2 3;
    intros id' EQ; destruct id'; intros H
    | |- context[match ?X as id return (?X = id -> _) with _ => _ end Logic.eq_refl] =>
    let EQ := fresh "EQ" in
    let id' := fresh "x" in
    generalize (Logic.eq_refl X); generalize X at 2 3;
    intros id' EQ; destruct id'
  end.

(* Restate nth_error function from Coq library. *)
Fixpoint nth_or_none {T: Type} (l: seq T) (n:nat) {struct n} : option T :=
  match n, l with
  | 0, x :: _ => Some x
  | n.+1, _ :: l => nth_or_none l n
  | _, _ => None
end.

(* Lemmas about nth_or_none. *)
Section NthOrNone.

  Context {T: eqType}.
  
  Lemma nth_or_none_mem :
    forall (l: seq T) n x, nth_or_none l n = Some x -> x \in l.
  Proof.
    induction l; first by unfold nth_or_none; ins; destruct n; ins.
    {
      ins; destruct n.
      {
        inversion H; subst.
        by rewrite in_cons eq_refl orTb.
      }
      simpl in H; rewrite in_cons; apply/orP; right.
      by apply IHl with (n := n).
    }
  Qed. 
    
  Lemma nth_or_none_mem_exists :
    forall (l: seq T) x, x \in l -> exists n, nth_or_none l n = Some x.
  Proof.
    induction l; first by intros x IN; rewrite in_nil in IN.
    {
      intros x IN; rewrite in_cons in IN.
      move: IN => /orP [/eqP EQ | IN]; first by subst; exists 0.
      specialize (IHl x IN); des.
      by exists n.+1.
    }
  Qed.
  
  Lemma nth_or_none_size_none :
    forall (l: seq T) n,
      nth_or_none l n = None <-> n >= size l.
  Proof.
    induction l; first by split; destruct n. 
    by destruct n; simpl; [by split; last by rewrite ltn0 | by rewrite ltnS].
  Qed.

  Lemma nth_or_none_size_some :
    forall (l: seq T) n x,
      nth_or_none l n = Some x -> n < size l.
  Proof.
    induction l; first by destruct n. 
    by intros n x; destruct n; simpl; last by rewrite ltnS; apply IHl.
  Qed.
  
  Lemma nth_or_none_uniq :
    forall (l: seq T) i j x,
      uniq l ->
      nth_or_none l i = Some x ->
      nth_or_none l j = Some x ->
      i = j.
  Proof.
    intros l i j x UNIQ SOMEi SOMEj.
    {
      generalize dependent j.
      generalize dependent i.
      induction l;
        first by ins; destruct i, j; simpl in *; inversion SOMEi.
      intros i SOMEi j SOMEj.
      simpl in UNIQ; move: UNIQ => /andP [NOTIN UNIQ].
      feed IHl; first by done.
      destruct i, j; simpl in *; first by done.
      - by inversion SOMEi; subst; apply nth_or_none_mem in SOMEj; rewrite SOMEj in NOTIN. 
      - by inversion SOMEj; subst; apply nth_or_none_mem in SOMEi; rewrite SOMEi in NOTIN.
      - by f_equal; apply IHl.
    }
  Qed.

Lemma nth_or_none_nth :
    forall (l: seq T) n x x0,
      nth_or_none l n = Some x ->
      nth x0 l n = x.
  Proof.
    induction l; first by destruct n.
    by intros n x x0 SOME; destruct n; simpl in *; [by inversion SOME | by apply IHl].
  Qed.

End NthOrNone.

(* Lemmas about big operators over Ordinals that use Ordinal functions. *)
Section BigOrdFunOrd.

  Definition fun_ord_to_nat {n} {T} (x0: T) (f: 'I_n -> T) : nat -> T.
  (* if x < n, apply the function f in the (Ordinal x: 'I_n), else return default x0. *)
    intro x; destruct (x < n) eqn:LT;
      [by apply (f (Ordinal LT)) | by apply x0].
  Defined.

  Lemma eq_fun_ord_to_nat :
    forall n {T: Type} x0 (f: 'I_n -> T) (x: 'I_n),
      (fun_ord_to_nat x0 f) x = f x.
  Proof.
    ins; unfold fun_ord_to_nat.
    des_eqrefl2.
      by f_equal; apply ord_inj.
      by destruct x; ins; rewrite i in EQ.
  Qed.

  Lemma eq_bigr_ord T n op idx r (P : pred 'I_n)
                    (F1: nat -> T) (F2: 'I_n -> T) :
    (forall i, P i -> F1 i = F2 i) ->
    \big[op/idx]_(i <- r | P i) F1 i = \big[op/idx]_(i <- r | P i) F2 i.
  Proof.
    induction r; ins; first by rewrite 2!big_nil.
    rewrite 2!big_cons; destruct (P a) eqn:EQ;
      by rewrite IHr; ins; rewrite H; ins.
  Qed.

  Lemma big_mkord_ord {T} {n} {op} {idx} x0 (P : pred 'I_n) (F: 'I_n -> T) :
    \big[op/idx]_(i < n | P i) F i =
      \big[op/idx]_(i < n | P i) (fun_ord_to_nat x0 F) i.
  Proof.
    have EQ := eq_bigr_ord T n op idx _ _ (fun_ord_to_nat x0 F) F.
    rewrite EQ; [by ins | by ins; rewrite eq_fun_ord_to_nat].
  Qed.

End BigOrdFunOrd.
  
(* Lemmas about the big concatenation operator. *)
Section BigCatLemmas.

  Lemma mem_bigcat_nat:
    forall (T: eqType) x m n j (f: _ -> list T),
      m <= j < n ->
      x \in (f j) ->
      x \in \cat_(m <= i < n) (f i).
  Proof.
    intros T x m n j f LE IN; move: LE => /andP LE; des.
    rewrite -> big_cat_nat with (n := j); simpl; [| by ins | by apply ltnW].
    rewrite mem_cat; apply/orP; right.
    destruct n; first by rewrite ltn0 in LE0.
    rewrite big_nat_recl; last by ins.
    by rewrite mem_cat; apply/orP; left.
  Qed.

  Lemma mem_bigcat_nat_exists :
    forall (T: eqType) x m n (f: nat -> list T),
      x \in \cat_(m <= i < n) (f i) ->
      exists i, x \in (f i) /\
                m <= i < n.
  Proof.
    intros T x m n f IN.
    induction n; first by rewrite big_geq // in IN.
    destruct (leqP m n); last by rewrite big_geq ?in_nil // ltnW in IN.
    rewrite big_nat_recr // /= mem_cat in IN.
    move: IN => /orP [HEAD | TAIL].
    {
      apply IHn in HEAD; destruct HEAD; exists x0; des.
      split; first by done.
      by apply/andP; split; [by done | by apply ltnW].
    }
    {
      exists n; split; first by done.
      apply/andP; split; [by done | by apply ltnSn].
    }
  Qed.
  
  Lemma mem_bigcat_ord:
    forall (T: eqType) x n (j: 'I_n) (f: 'I_n -> list T),
      j < n ->
      x \in (f j) ->
      x \in \cat_(i < n) (f i).
  Proof.
    intros T x n j f LE IN; rewrite (big_mkord_ord nil).
    rewrite -(big_mkord (fun x => true)).
    apply mem_bigcat_nat with (j := j);
      [by apply/andP; split | by rewrite eq_fun_ord_to_nat].
  Qed.

  Lemma mem_bigcat_ord_exists :
    forall (T: eqType) x n (f: 'I_n -> list T),
      x \in \cat_(i < n) (f i) ->
      exists i, x \in (f i).
  Proof.
    intros T x n f IN.
    induction n; first by rewrite big_ord0 in_nil in IN.
    {
      rewrite big_ord_recr /= mem_cat in IN.
      move: IN => /orP [HEAD | TAIL].
      {
        apply IHn in HEAD; destruct HEAD as [x0 IN].
        by eexists (widen_ord _ x0); apply IN.
      }
      {
        by exists ord_max; desf.
      }
    }
  Qed.

  Lemma bigcat_ord_uniq :
    forall (T: eqType) n (f: 'I_n -> list T),
      (forall i, uniq (f i)) ->
      (forall x i1 i2,
         x \in (f i1) -> x \in (f i2) -> i1 = i2) ->
      uniq (\cat_(i < n) (f i)).
  Proof.
    intros T n f SINGLE UNIQ.
    induction n; first by rewrite big_ord0.
    {
      rewrite big_ord_recr cat_uniq; apply/andP; split.
      {
        apply IHn; first by done.
        intros x i1 i2 IN1 IN2.
        exploit (UNIQ x);
          [by apply IN1 | by apply IN2 | intro EQ; inversion EQ].
        by apply ord_inj.
      }
      apply /andP; split; last by apply SINGLE.
      {
        rewrite -all_predC; apply/allP; intros x INx.

        simpl; apply/negP; unfold not; intro BUG.
        rewrite -big_ord_narrow in BUG.
        rewrite big_mkcond /= in BUG.
        have EX := mem_bigcat_ord_exists T x n.+1 _.
        apply EX in BUG; clear EX; desf.
        apply UNIQ with (i1 := ord_max) in BUG; last by done.
        by desf; unfold ord_max in *; rewrite /= ltnn in Heq.
      }
    }
  Qed.

  Lemma map_bigcat_ord {T} {T'} n (f: 'I_n -> seq T) (g: T -> T') :
    map g (\cat_(i < n) (f i)) = \cat_(i < n) (map g (f i)).
  Proof.
    destruct n; first by rewrite 2!big_ord0. 
    induction n; first by rewrite 2!big_ord_recr 2!big_ord0.
    rewrite big_ord_recr [\cat_(cpu < n.+2)_]big_ord_recr /=.
    by rewrite map_cat; f_equal; apply IHn.
  Qed.

  Lemma size_bigcat_ord {T} n (f: 'I_n -> seq T) :
    size (\cat_(i < n) (f i)) = \sum_(i < n) (size (f i)).
  Proof.
    destruct n; first by rewrite 2!big_ord0.
    induction n; first by rewrite 2!big_ord_recr 2!big_ord0 /= add0n.
    rewrite big_ord_recr [\sum_(i0 < n.+2)_]big_ord_recr size_cat /=.
    by f_equal; apply IHn.
  Qed.

  Lemma size_bigcat_ord_max {T} n (f: 'I_n -> seq T) m :
    (forall x, size (f x) <= m) ->
    size (\cat_(i < n) (f i)) <= m*n.
  Proof.
    intros SIZE.
    rewrite size_bigcat_ord.
    apply leq_trans with (n := \sum_(i0 < n) m);
      last by rewrite big_const_ord iter_addn addn0.
    by apply leq_sum; ins; apply SIZE. 
  Qed.
  
End BigCatLemmas.

(* Induction lemmas for natural numbers. *)
Section NatInduction.
  
  Lemma strong_ind :
    forall (P: nat -> Prop),
      (forall n, (forall k, k < n -> P k) -> P n) ->
      forall n, P n.
  Proof.
    intros P ALL n; apply ALL.
    induction n; first by ins; apply ALL.
    intros k LTkSn; apply ALL.
    by intros k0 LTk0k; apply IHn, leq_trans with (n := k).
  Qed.

  Lemma leq_as_delta :
    forall x1 (P: nat -> Prop),
      (forall x2, x1 <= x2 -> P x2) <->
      (forall delta, P (x1 + delta)).
  Proof.
    ins; split; last by intros ALL x2 LE; rewrite -(subnK LE) addnC; apply ALL.
    {
      intros ALL; induction delta.
        by rewrite addn0; apply ALL, leqnn. 
        by apply ALL; rewrite -{1}[x1]addn0; apply leq_add; [by apply leqnn | by ins]. 
    }
  Qed.
  
End NatInduction.

(* Lemmas about basic arithmetic. *)
Section Arithmetic.
  
  Lemma addnb (b1 b2 : bool) : (b1 + b2) != 0 = b1 || b2.
  Proof.
    by destruct b1,b2;
    rewrite ?addn0 ?add0n ?addn1 ?orTb ?orbT ?orbF ?orFb.
  Qed.

  Lemma subh1 :
    forall m n p,
      m >= n ->
      m - n + p = m + p - n.
  Proof.
    by ins; ssromega.
  Qed.

  Lemma subh2 :
    forall m1 m2 n1 n2,
      m1 >= m2 ->
      n1 >= n2 ->
      (m1 + n1) - (m2 + n2) = m1 - m2 + (n1 - n2).
  Proof.
    by ins; ssromega.
  Qed.

  Lemma subh3 :
    forall m n p,
      m + p <= n ->
      n >= p ->
      m <= n - p.
  Proof.
    ins. rewrite <- leq_add2r with (p := p).
    by rewrite subh1 // -addnBA // subnn addn0.
  Qed.

  Lemma subh4:
    forall m n p,
      m <= n ->
      p <= n ->
      (m == n - p) = (p == n - m).
  Proof.
    intros; apply/eqP.
    destruct (p == n - m) eqn:EQ.
      by move: EQ => /eqP EQ; rewrite EQ subKn.
      by apply negbT in EQ; unfold not; intro BUG;
        rewrite BUG subKn ?eq_refl in EQ.
  Qed.

  Lemma addmovr:
    forall m n p,
      m >= n ->
      (m - n = p <-> m = p + n).
  Proof.
    by split; ins; ssromega.
  Qed.

  Lemma addmovl:
    forall m n p,
      m >= n ->
      (p = m - n <-> p + n = m).
  Proof.
    by split; ins; ssromega.
  Qed.

  Lemma ltn_div_trunc :
    forall m n d,
      d > 0 ->
      m %/ d < n %/ d ->
      m < n.
  Proof.
    intros m n d GT0 DIV; rewrite ltn_divLR in DIV; last by ins.
    by apply leq_trans with (n := n %/ d * d);
      [by ins| by apply leq_trunc_div].
  Qed.
  
  Lemma subndiv_eq_mod:
    forall n d, n - n %/ d * d = n %% d.
  Proof.
    by ins; rewrite {1}(divn_eq n d) addnC -addnBA // subnn addn0.
  Qed.

  Lemma ltSnm : forall n m, n.+1 < m -> n < m.
  Proof.
    by ins; apply ltn_trans with (n := n.+1); [by apply ltnSn |by ins].
  Qed.

  Lemma divSn_cases :
    forall n d,
      d > 1 ->
      (n %/ d = n.+1 %/d /\ n %% d + 1 = n.+1 %% d) \/
      (n %/ d + 1 = n.+1 %/ d).
  Proof.
    ins; set x := n %/ d; set y := n %% d.
    assert (GT0: d > 0); first by apply ltn_trans with (n := 1).
    destruct (ltngtP y (d - 1)) as [LTN | BUG | GE]; [left | | right];
      first 1 last.
    {
      exploit (@ltn_pmod n d); [by apply GT0 | intro LTd; fold y in LTd].
      rewrite -(ltn_add2r 1) [y+1]addn1 ltnS in BUG.
      rewrite subh1 in BUG; last by apply GT0.
      rewrite -addnBA // subnn addn0 in BUG.
      by apply (leq_ltn_trans BUG) in LTd; rewrite ltnn in LTd.
    }

    {
      (* Case 1: y = d - 1*)
      move: GE => /eqP GE; rewrite -(eqn_add2r 1) in GE.
      rewrite subh1 in GE; last by apply GT0.
      rewrite -addnBA // subnn addn0 in GE.
      move: GE => /eqP GE.
      apply f_equal with (f := fun x => x %/ d) in GE.
      rewrite divnn GT0 /= in GE.
      unfold x; rewrite -GE.
      rewrite -divnMDl; last by apply GT0.
      f_equal; rewrite addnA.
      by rewrite -divn_eq addn1.
    }
    {
      assert (EQDIV: n %/ d = n.+1 %/ d).
      {
        apply/eqP; rewrite eqn_leq; apply/andP; split;
          first by apply leq_div2r, leqnSn.
        rewrite leq_divRL; last by apply GT0.
        rewrite -ltnS {2}(divn_eq n.+1 d).
        rewrite -{1}[_ %/ d * d]addn0 ltn_add2l.
        unfold y in *.
        rewrite ltnNge; apply/negP; unfold not; intro BUG.
        rewrite leqn0 in BUG; move: BUG => /eqP BUG.
        rewrite -(modnn d) -addn1 in BUG.
        destruct d; first by rewrite sub0n in LTN.
        move: BUG; move/eqP; rewrite -[d.+1]addn1 eqn_modDr [d+1]addn1; move => /eqP BUG.
        rewrite BUG -[d.+1]addn1 -addnBA // subnn addn0 in LTN.
        by rewrite modn_small in LTN;
          [by rewrite ltnn in LTN | by rewrite addn1 ltnSn].
      }
      (* Case 2: y < d - 1 *)
      split; first by rewrite -EQDIV.
      {
        unfold x, y in *.
        rewrite -2!subndiv_eq_mod.
        rewrite subh1 ?addn1; last by apply leq_trunc_div.
        rewrite EQDIV; apply/eqP.
        rewrite -(eqn_add2r (n%/d*d)).
        by rewrite subh1; last by apply leq_trunc_div.
      }
    }
  Qed.

  Lemma ceil_neq0 :
    forall x y,
      x > 0 ->
      y > 0 ->
      div_ceil x y > 0.
  Proof.
    unfold div_ceil; intros x y GEx GEy.
    destruct (y %| x) eqn:DIV; last by done.
    by rewrite divn_gt0; first by apply dvdn_leq.
  Qed.

  Lemma leq_divceil2r :
    forall d m n,
      d > 0 ->
      m <= n ->
      div_ceil m d <= div_ceil n d.
  Proof.
    unfold div_ceil; intros d m n GT0 LE.
    destruct (d %| m) eqn:DIVm, (d %| n) eqn:DIVn;
      [by apply leq_div2r | | | by apply leq_div2r].
    by apply leq_trans with (n := n %/ d); first by apply leq_div2r.
    {
      rewrite leq_eqVlt in LE; move: LE => /orP [/eqP EQ | LT];
        first by subst; rewrite DIVn in DIVm.
      rewrite ltn_divLR //.
      apply leq_trans with (n := n); first by done.
      by apply eq_leq; symmetry; apply/eqP; rewrite -dvdn_eq.    
    }
  Qed.
  
  Lemma min_lt_same :
    forall x y z,
      minn x z < minn y z -> x < y.
  Proof.
    unfold minn; ins; desf.
    {
      apply negbT in Heq0; rewrite -ltnNge in Heq0.
      by apply leq_trans with (n := z).
    }
    {
      apply negbT in Heq; rewrite -ltnNge in Heq.
      by apply (ltn_trans H) in Heq0; rewrite ltnn in Heq0.
    }
    by rewrite ltnn in H.
  Qed.
  
End Arithmetic.

(* Lemmas about arithmetic with sums. *)
Section SumArithmetic.

  (* Inequality with sums is monotonic with their functions. *)
  Lemma sum_diff_monotonic :
    forall n G F,
      (forall i : nat, i < n -> G i <= F i) ->
      (\sum_(0 <= i < n) (G i)) <= (\sum_(0 <= i < n) (F i)).
  Proof.
    intros n G F ALL.
    rewrite big_nat_cond [\sum_(0 <= i < n) F i]big_nat_cond.
    apply leq_sum; intros i LT; rewrite andbT in LT.
    move: LT => /andP LT; des.
    by apply ALL, leq_trans with (n := n); ins.
  Qed.

  Lemma sum_diff :
    forall n F G,
      (forall i (LT: i < n), F i >= G i) ->
      \sum_(0 <= i < n) (F i - G i) =
        (\sum_(0 <= i < n) (F i)) - (\sum_(0 <= i < n) (G i)).       
  Proof.
    intros n F G ALL.
    induction n; ins; first by rewrite 3?big_geq.
    assert (ALL': forall i, i < n -> G i <= F i).
      by ins; apply ALL, leq_trans with (n := n); ins.
    rewrite 3?big_nat_recr // IHn //; simpl.
    rewrite subh1; last by apply sum_diff_monotonic.
    rewrite subh2 //; try apply sum_diff_monotonic; ins.
    rewrite subh1; ins; apply sum_diff_monotonic; ins.
    by apply ALL; rewrite ltnS leqnn. 
  Qed.

  Lemma prev_le_next :
    forall (T: Type) (F: T->nat) r (x0: T) i k,
      (forall i, i < (size r).-1 -> F (nth x0 r i) <= F (nth x0 r i.+1)) ->
      (i + k <= (size r).-1) ->
      F (nth x0 r i) <= F (nth x0 r (i+k)).
  Proof.
    intros T F r x0 i k ALL SIZE.
    generalize dependent i. generalize dependent k.
    induction k; intros; first by rewrite addn0 leqnn.
    specialize (IHk i.+1); exploit IHk; [by rewrite addSnnS | intro LE].
    apply leq_trans with (n := F (nth x0 r (i.+1)));
      last by rewrite -addSnnS.
    apply ALL, leq_trans with (n := i + k.+1); last by ins.
    by rewrite addnS ltnS leq_addr.
  Qed.

  Lemma telescoping_sum :
    forall (T: Type) (F: T->nat) r (x0: T),
    (forall i, i < (size r).-1 -> F (nth x0 r i) <= F (nth x0 r i.+1)) ->
      F (nth x0 r (size r).-1) - F (nth x0 r 0) =
        \sum_(0 <= i < (size r).-1) (F (nth x0 r (i.+1)) - F (nth x0 r i)).
  Proof.
    intros T F r x0 ALL.
    have ADD1 := big_add1.
    have RECL := big_nat_recl.
    specialize (ADD1 nat 0 addn 0 (size r) (fun x => true) (fun i => F (nth x0 r i))).
    specialize (RECL nat 0 addn (size r).-1 0 (fun i => F (nth x0 r i))).
    rewrite sum_diff; last by ins.
    rewrite addmovr; last by rewrite -[_.-1]add0n; apply prev_le_next; try rewrite add0n leqnn.
    rewrite subh1; last by apply sum_diff_monotonic.
    rewrite addnC -RECL //.
    rewrite addmovl; last by rewrite big_nat_recr // -{1}[\sum_(_ <= _ < _) _]addn0; apply leq_add.
    by rewrite addnC -big_nat_recr.
  Qed.

End SumArithmetic.


Section FixedPoint.
  
  Lemma iter_fix T (F : T -> T) x k n :
    iter k F x = iter k.+1 F x ->
    k <= n ->
    iter n F x = iter n.+1 F x.
  Proof.
    move => e. elim: n. rewrite leqn0. by move/eqP<-.
    move => n IH. rewrite leq_eqVlt; case/orP; first by move/eqP<-.
    move/IH => /= IHe. by rewrite -!IHe.
  Qed.

  Lemma fun_mon_iter_mon :
    forall (f: nat -> nat) x0 x1 x2,
      x1 <= x2 ->
      f x0 >= x0 ->
      (forall x1 x2, x1 <= x2 -> f x1 <= f x2) ->
      iter x1 f x0 <= iter x2 f x0.
  Proof.
    intros f x0 x1 x2 LE MIN MON.
    revert LE; revert x2; rewrite leq_as_delta; intros delta.
    induction x1; try rewrite add0n.
    {
      induction delta; first by apply leqnn.
      apply leq_trans with (n := iter delta f x0); first by done.
      clear IHdelta.
      induction delta; first by done.
      {
        rewrite 2!iterS; apply MON.
        apply IHdelta.
      }
    }
    {
      rewrite iterS -addn1 -addnA [1 + delta]addnC addnA addn1 iterS.
      by apply MON, IHx1.
    }
  Qed.

  Lemma fun_mon_iter_mon_helper :
    forall T (f: T -> T) (le: rel T) x0 x1,
      reflexive le ->
      transitive le ->
      (forall x2, le x0 (iter x2 f x0)) ->
      (forall x1 x2, le x0 x1 -> le x1 x2 -> le (f x1) (f x2)) ->
      le (iter x1 f x0) (iter x1.+1 f x0).
  Proof.
    intros T f le x0 x1 REFL TRANS MIN MON.
    generalize dependent x0.
    induction x1; first by ins; apply (MIN 1).
    by ins; apply MON; [by apply MIN | by apply IHx1].
  Qed.

  Lemma fun_mon_iter_mon_generic :
    forall T (f: T -> T) (le: rel T) x0 x1 x2,
      reflexive le ->
      transitive le ->
      x1 <= x2 ->
      (forall x1 x2, le x0 x1 -> le x1 x2 -> le (f x1) (f x2)) ->
      (forall x2 : nat, le x0 (iter x2 f x0)) ->
      le (iter x1 f x0) (iter x2 f x0).
  Proof.
    intros T f le x0 x1 x2 REFL TRANS LE MON MIN.
    revert LE; revert x2; rewrite leq_as_delta; intros delta.
    induction delta; first by rewrite addn0; apply REFL.
    apply (TRANS) with (y := iter (x1 + delta) f x0);
      first by apply IHdelta.
    by rewrite addnS; apply fun_mon_iter_mon_helper.
  Qed.

End FixedPoint.

(* Lemmas about sorted lists. *)
Section Sorting.
  
  Lemma sorted_rcons_prefix :
    forall {T: eqType} (leT: rel T) s x,
      sorted leT (rcons s x) ->
      sorted leT s.
  Proof.
    intros T leT s x SORT; destruct s; simpl; first by ins.
    rewrite rcons_cons /= rcons_path in SORT.
    by move: SORT => /andP [PATH _].
  Qed.

  Lemma order_sorted_rcons :
    forall {T: eqType} (leT: rel T) (s: seq T) (x last: T),
      transitive leT ->
      sorted leT (rcons s last) ->
      x \in s ->
      leT x last.
  Proof.
    intros T leT s x last TRANS SORT IN.
    induction s; first by rewrite in_nil in IN.
    simpl in SORT; move: IN; rewrite in_cons; move => /orP IN.
    destruct IN as [HEAD | TAIL];
      last by apply IHs; [by apply path_sorted in SORT| by ins].
    move: HEAD => /eqP HEAD; subst a.
    apply order_path_min in SORT; last by ins.
    move: SORT => /allP SORT.
    by apply SORT; rewrite mem_rcons in_cons; apply/orP; left.
  Qed.
  
  Lemma sorted_lt_idx_implies_rel :
    forall {T: eqType} (leT: rel T) (s: seq T) x0 i1 i2,
      transitive leT ->
      sorted leT s ->
      i1 < i2 ->
      i2 < size s ->
      leT (nth x0 s i1) (nth x0 s i2).
  Proof.
    intros T leT s x0 i1 i2 TRANS SORT LE LEsize.
    generalize dependent i2; rewrite leq_as_delta.
    intros delta LT.
    destruct s; first by rewrite ltn0 in LT.
    simpl in SORT.
    induction delta;
      first by rewrite /= addn0 ltnS in LT; rewrite addn0; apply/pathP.
    {
      rewrite /transitive (TRANS (nth x0 (s :: s0) (i1.+1 + delta))) //;
        first by apply IHdelta, leq_ltn_trans with (n := i1.+1 + delta.+1); [rewrite leq_add2l|].
      rewrite -[delta.+1]addn1 addnA addn1; apply/pathP; first by done.
      by rewrite /= -[delta.+1]addn1 addnA addn1 ltnS in LT.
    }  
  Qed.

  Lemma sorted_uniq_rel_implies_le_idx :
    forall {T: eqType} (leT: rel T) (s: seq T) x0 i1 i2,
      irreflexive leT ->
      transitive leT ->
      sorted leT s ->
      leT (nth x0 s i1) (nth x0 s i2) ->
      i1 < size s ->
      i2 < size s ->
      i1 <= i2.
  Proof.
    intros T leT s x0 i1 i2 IRR TRANS SORT REL SIZE1 SIZE2.
    generalize dependent i2.
    induction i1; first by done.
    {
      intros i2 REL SIZE2.
      feed IHi1; first by apply ltn_trans with (n := i1.+1).
      apply leq_trans with (n := i1.+1); first by done.
      rewrite ltn_neqAle; apply/andP; split.
      {
        apply/eqP; red; intro BUG; subst.
        assert (REL': leT (nth x0 s i2) (nth x0 s i2)).
        {
          rewrite /transitive (TRANS (nth x0 s i2.+1)) //.
          by apply sorted_lt_idx_implies_rel; rewrite // ltnSn.
        }
        by rewrite /irreflexive IRR in REL'.
      }
      {
        apply IHi1; last by done.
        rewrite /transitive (TRANS (nth x0 s i1.+1)) //.
        by apply sorted_lt_idx_implies_rel; try (by done); apply ltnSn.
      }
    }
  Qed.

End Sorting.

(* Lemmas about lists without duplicates. *)
Section UniqList.

  Lemma idx_lt_rcons :
    forall {T: eqType} (l: seq T) i x0,
      uniq l ->
      i < size l ->
      [seq x <- l | index x l < i.+1] =
        rcons [seq x <- l | index x l < i] (nth x0 l i).
  Proof.
    intros T l i x0 UNIQ LT.
    generalize dependent i.
    induction l as [| l' x] using last_ind; first by ins; rewrite ltn0 in LT.
    {
      intros i LT.
      rewrite size_rcons in LT.
      rewrite filter_rcons.
      rewrite -cats1 index_cat; desf; simpl in *;
        try (by rewrite rcons_uniq in UNIQ; move: UNIQ => /andP [NOTIN _]; rewrite Heq0 in NOTIN).
      {
        rewrite eq_refl addn0 in Heq.
        rewrite filter_cat /=.
        assert (EQ: i = size l'); first by apply/eqP; rewrite eqn_leq; apply/andP; split.
        rewrite index_cat Heq0 /= eq_refl addn0 EQ ltnn cats0.
        rewrite nth_cat ltnn subnn /=.
        f_equal; apply eq_in_filter; red; intros y INy.
        by rewrite index_cat INy ltnS index_size index_mem INy.
      }
      {
        rewrite rcons_uniq in UNIQ; move: UNIQ => /andP [NOTIN UNIQ].
        rewrite eq_refl addn0 in Heq.
        apply negbT in Heq; rewrite -leqNgt in Heq.
        rewrite nth_cat Heq.
        rewrite filter_cat /= index_cat Heq0 /= eq_refl addn0.
        rewrite ltnS in LT; rewrite ltnNge LT /= cats0 cats1.
        apply eq_trans with (y := [seq x1 <- l' | index x1 l' < i.+1]);
          first by apply eq_in_filter; red; intros y INy; rewrite -cats1 index_cat INy.
        rewrite IHl //; f_equal; apply eq_in_filter; intros y INy.
        by rewrite -cats1 index_cat INy.
      }
    }
  Qed.
  
  Lemma filter_idx_lt_take :
    forall {T: eqType} (l: seq T) i,
      uniq l ->
      i < size l ->
      [seq x <- l | index x l < i] = take i l.
  Proof.
    intros T l i UNIQ LT.
    generalize dependent l.
    induction i.
    {
      intros l UNIQ LT; destruct l as [| x0 l']; first by done.
      by apply eq_trans with (filter pred0 (x0 :: l'));
        [by apply eq_filter | by rewrite filter_pred0].
    }
    {
      intros l UNIQ LT.
      destruct (lastP l) as [| l' x]; first by rewrite ltn0 in LT.
      rewrite size_rcons ltnS in LT.
      rewrite (take_nth x); last by rewrite size_rcons; apply (leq_trans LT).
      rewrite -> idx_lt_rcons with (x0 := x); try (by done);
        last by rewrite size_rcons; apply (leq_trans LT).
      by f_equal; apply IHi; last by rewrite size_rcons; apply (leq_trans LT).
    }  
  Qed.

  Lemma filter_idx_le_takeS :
    forall {T: eqType} (l: seq T) i,
      uniq l ->
      i < size l ->
      [seq x <- l | index x l <= i] = take i.+1 l.
  Proof.
    intros T l i UNIQ LT.
    induction l as [| x0 l]; first by done.
    simpl; rewrite eq_refl leq0n; f_equal.
    apply eq_trans with (y := [seq x <- l | index x l < i]).
    {
      apply eq_in_filter; red; intros x IN.
      desf; subst; last by done.
      by simpl in *; rewrite IN andFb in UNIQ.
    }
    simpl in *; desf.
    rewrite /= ltnS in LT.
    rewrite leq_eqVlt in LT; desf.
    {
      rewrite take_size.
      apply eq_trans with (y := filter predT l); last by rewrite filter_predT.
      by apply eq_in_filter; red; ins; rewrite index_mem.
    }
    by apply filter_idx_lt_take.
  Qed.
  
End UniqList.
  
Section PowerSet.
  
  (* Based on https://www.ps.uni-saarland.de/formalizations/fset/html/libs.fset.html *)
  Definition powerset {T: eqType} (l: seq T) : seq (seq T) :=
    let mT := ((size l).-tuple bool) in
      (map (fun m : mT => (mask m l)) (enum {: mT})).

  Lemma mem_powerset {T: eqType} (x: seq T) y :
    y \in (powerset x) -> {subset y <= x}.          
  Proof.
    intros POW; red; intros z IN; unfold powerset in POW.
    move: POW => /mapP POW; destruct POW as [pair POW EQ]; subst.
    by apply mem_mask with (m := pair).
  Qed.

End PowerSet.

(* Additional lemmas about list zip. *)
Section Zip.
  
  Lemma zipP {T: eqType} (P: _ -> _ -> bool) (X Y: seq T) x0:
    size X = size Y ->
    reflect (forall i, i < size (zip X Y) -> P (nth x0 X i) (nth x0 Y i))
            (all (fun p => P (fst p) (snd p)) (zip X Y)).
  Proof.
    intro SIZE; apply/introP.
    {
      move => /allP ALL i LT.
      apply (ALL (nth x0 X i,nth x0 Y i)).
      by rewrite -nth_zip; [by apply mem_nth | by done].
    }
    {
      rewrite -has_predC; unfold predC.
      move => /hasP HAS; simpl in *; destruct HAS as [x IN NOT].
      unfold not; intro BUG.
      exploit (BUG (index x (zip X Y))).
        by rewrite index_mem.
      have NTH := @nth_zip _ _ x0 x0 X Y (index x (zip X Y)) SIZE.
      destruct x as [x1 x2].
      rewrite {1}nth_index in NTH; last by done.
      clear BUG; intros BUG.
      inversion NTH as [[NTH0 NTH1]]; rewrite -NTH0 in NTH1.
      by rewrite -NTH0 -NTH1 in BUG; rewrite BUG in NOT.
    }
  Qed.

  Lemma mem_zip_exists :
    forall (T T': eqType) (x1: T) (x2: T') l1 l2 elem elem',
      size l1 = size l2 ->
      (x1, x2) \in zip l1 l2 ->
      exists idx,
        idx < size l1 /\
        idx < size l2 /\
        x1 = nth elem l1 idx /\
        x2 = nth elem' l2 idx.
  Proof.
    intros T T' x1 x2 l1 l2 elem elem' SIZE IN.
    assert (LT: index (x1, x2) (zip l1 l2) < size l1).
    {
      apply leq_trans with (n := size (zip l1 l2)); first by rewrite index_mem.
      by rewrite size_zip; apply geq_minl.
    }
    have NTH := @nth_index _ (elem,elem') (x1, x2) (zip l1 l2) IN.
    rewrite nth_zip in NTH; last by done.
    inversion NTH; rewrite H1 H0; rewrite H0 in H1.
    by exists (index (x1, x2) (zip l1 l2)); repeat split; try (by done); rewrite -?SIZE.
  Qed.

End Zip.

(* Additional lemmas about sum and max big operators. *)
Section ExtraLemmasSumMax.
  
  Lemma leq_big_max I r (P : pred I) (E1 E2 : I -> nat) :
    (forall i, P i -> E1 i <= E2 i) ->
      \max_(i <- r | P i) E1 i <= \max_(i <- r | P i) E2 i.
  Proof.
    move => leE12; elim/big_ind2 : _ => // m1 m2 n1 n2.
    intros LE1 LE2; rewrite leq_max; unfold maxn.
    by destruct (m2 < n2) eqn:LT; [by apply/orP; right | by apply/orP; left].
  Qed.

  Lemma sum_nat_eq0_nat (T : eqType) (F : T -> nat) (r: seq T) :
    all (fun x => F x == 0) r = (\sum_(i <- r) F i == 0).
  Proof.
    destruct (all (fun x => F x == 0) r) eqn:ZERO.
    {
      move: ZERO => /allP ZERO; rewrite -leqn0.
      rewrite big_seq_cond (eq_bigr (fun x => 0));
        first by rewrite big_const_seq iter_addn mul0n addn0 leqnn.
      intro i; rewrite andbT; intros IN.
      specialize (ZERO i); rewrite IN in ZERO.
      by move: ZERO => /implyP ZERO; apply/eqP; apply ZERO.
    }
    {
      apply negbT in ZERO; rewrite -has_predC in ZERO.
      move: ZERO => /hasP ZERO; destruct ZERO as [x IN NEQ]; simpl in NEQ.
      rewrite (big_rem x) /=; last by done.
      symmetry; apply negbTE; rewrite neq_ltn; apply/orP; right.
      apply leq_trans with (n := F x); last by apply leq_addr.
      by rewrite lt0n.
    }
  Qed.
  
  Lemma extend_sum :
    forall t1 t2 t1' t2' F,
      t1' <= t1 ->
      t2 <= t2' ->
      \sum_(t1 <= t < t2) F t <= \sum_(t1' <= t < t2') F t.
  Proof.
    intros t1 t2 t1' t2' F LE1 LE2.
    destruct (t1 <= t2) eqn:LE12;
      last by apply negbT in LE12; rewrite -ltnNge in LE12; rewrite big_geq // ltnW.
    rewrite -> big_cat_nat with (m := t1') (n := t1); try (by done); simpl;
      last by apply leq_trans with (n := t2).
    rewrite -> big_cat_nat with (p := t2') (n := t2); try (by done); simpl.
    by rewrite addnC -addnA; apply leq_addr.
  Qed.
  
End ExtraLemmasSumMax.

(* Lemmas about the finite existencial for Ordinals [exists, ...]. *)
Section OrdExists.

  Lemma exists_ord0:
    forall (T: eqType) P,
      [exists x in 'I_0, P x] = false.
  Proof.
    intros T P.
    apply negbTE; rewrite negb_exists; apply/forall_inP.
    intros x; destruct x as [x LT].
    by exfalso; rewrite ltn0 in LT.
  Qed.

  Lemma exists_recr:
    forall (T: eqType) n P,
      [exists x in 'I_n.+1, P x] =
      [exists x in 'I_n, P (widen_ord (leqnSn n) x)] || P (ord_max).
  Proof.
    intros t n P.
    apply/idP/idP.
    {
      move => /exists_inP EX; destruct EX as [x IN Px].
      destruct x as [x LT].
      remember LT as LT'; clear HeqLT'. 
      rewrite ltnS leq_eqVlt in LT; move: LT => /orP [/eqP EQ | LT].
      {
        apply/orP; right.
        unfold ord_max; subst x.
        apply eq_trans with (y := P (Ordinal LT')); last by done.
        by f_equal; apply ord_inj.
      }
      {
        apply/orP; left.
        apply/exists_inP; exists (Ordinal LT); first by done.
        apply eq_trans with (y := P (Ordinal LT')); last by done.
        by f_equal; apply ord_inj.
      }
    }
    {
      intro OR; apply/exists_inP.
      move: OR => /orP [/exists_inP EX | MAX].
      {
        by destruct EX as [x IN Px]; exists (widen_ord (leqnSn n) x).
      }
      by exists ord_max.
    }
  Qed.

End OrdExists.

(* Additional lemmas about counting. *)
Section Counting.
  
  Lemma count_or :
    forall (T: eqType) (l: seq T) P Q,
      count (fun x => P x || Q x) l <= count P l + count Q l. 
  Proof.
    intros T l P Q; rewrite -count_predUI.
    apply leq_trans with (n := count (predU P Q) l);
      last by apply leq_addr.
    by apply sub_count; red; unfold predU; simpl.
  Qed.

  Lemma sub_in_count :
    forall (T: eqType) (l: seq T) (P1 P2: T -> bool),
      (forall x, x \in l -> P1 x -> P2 x) ->
      count P1 l <= count P2 l.
  Proof.
    intros T l P1 P2 SUB.
    apply leq_trans with (n := count (fun x => P1 x && (x \in l)) l);
      first by apply eq_leq, eq_in_count; red; move => x INx; rewrite INx andbT.
    by apply sub_count; red; move => x /andP [Px INx]; apply SUB.
  Qed.

  Lemma count_sub_uniqr :
    forall (T: eqType) (l1 l2: seq T) P,
      uniq l1 ->
      {subset l1 <= l2} ->
      count P l1 <= count P l2.
  Proof.
    intros T l1 l2 P UNIQ SUB.
    rewrite -!size_filter uniq_leq_size ?filter_uniq // => x.
    by rewrite !mem_filter =>/andP [-> /SUB].
  Qed.

  Lemma count_pred_inj :
    forall (T: eqType) (l: seq T) (P: T -> bool),
      uniq l ->
      (forall x1 x2, P x1 -> P x2 -> x1 = x2) ->
      count P l <= 1.
  Proof.
    intros T l P UNIQ INJ.
    induction l as [| x l']; [by done | simpl in *].
    {
      move: UNIQ => /andP [NOTIN UNIQ].
      specialize (IHl' UNIQ).
      rewrite leq_eqVlt in IHl'.
      move: IHl' => /orP [/eqP ONE | ZERO]; last first.
      {
        rewrite ltnS leqn0 in ZERO.
        by move: ZERO => /eqP ->; rewrite addn0 leq_b1.
      }
      destruct (P x) eqn:Px; last by rewrite add0n ONE.
      {
        move: ONE => /eqP ONE.
        rewrite eqn_leq in ONE; move: ONE => /andP [_ ONE].
        rewrite -has_count in ONE.
        move: ONE => /hasP ONE; destruct ONE as [y IN Py].
        specialize (INJ x y Px Py); subst.
        by rewrite IN in NOTIN.
      }
    }
  Qed.

  Lemma count_exists :
    forall (T: eqType) (l: seq T) n (P: T -> 'I_n -> bool),
      uniq l ->
      (forall y x1 x2, P x1 y -> P x2 y -> x1 = x2) ->
      count (fun (y: T) => [exists x in 'I_n, P y x]) l <= n.
  Proof.
    intros T l n P UNIQ INJ.
    induction n.
    {
      apply leq_trans with (n := count pred0 l); last by rewrite count_pred0.
      apply sub_count; red; intro x.
      by rewrite exists_ord0 //.
    }
    {
      apply leq_trans with (n := n + 1); last by rewrite addn1.
      apply leq_trans with (n := count (fun y => [exists x in 'I_n, P y (widen_ord (leqnSn n) x)] || P y ord_max) l).
      {
        apply eq_leq, eq_count; red; intro x.
        by rewrite exists_recr //.
      }
      eapply (leq_trans (count_or _ _ _ _)).
      apply leq_add.
      {
        apply IHn.
        {
          intros y x1 x2 P1 P2.
          by specialize (INJ (widen_ord (leqnSn n) y) x1 x2 P1 P2).
        }
      }
      {
        apply count_pred_inj; first by done.
        by intros x1 x2 P1 P2; apply INJ with (y := ord_max). 
      }
    }
  Qed.

End Counting.