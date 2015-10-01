Require Import Vbase ssreflect ssrbool eqtype ssrnat seq fintype bigop tuple path div ssromega.

Section Pair.

Context {A B: Type}.
Variable p: A * B.
Definition pair_1st := fst p.
Definition pair_2nd := snd p.

End Pair.

Section Triple.

Context {A B C: Type}.
Variable p: A * B * C.
Definition triple_1st (p: A * B * C) := fst (fst p).
Definition triple_2nd := snd (fst p).
Definition triple_3rd := snd p.

End Triple.

Reserved Notation "\cat_ ( m <= i < n ) F"
  (at level 41, F at level 41, i, m, n at level 50,
   format "'[' \cat_ ( m <= i < n ) '/ ' F ']'").

Notation "\cat_ ( m <= i < n ) F" :=
  (\big[cat/[::]]_(m <= i < n) F%N) : nat_scope.

Reserved Notation "\cat_ ( i < n ) F"
  (at level 41, F at level 41, i, n at level 50,
   format "'[' \cat_ ( i < n ) '/ ' F ']'").

Notation "\cat_ ( i < n ) F" :=
  (\big[cat/[::]]_(i < n) F%N) : nat_scope.

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

Lemma mem_bigcat_nat:
  forall (T: eqType) x m n j (f: _ -> list T)
         (LE: m <= j < n) (IN: x \in (f j)),
  x \in \cat_(m <= i < n) (f i).
Proof.
  ins; move: LE => /andP LE; des.
  rewrite -> big_cat_nat with (n := j); simpl; [| by ins | by apply ltnW].
  rewrite mem_cat; apply/orP; right.
  destruct n; first by rewrite ltn0 in LE0.
  rewrite big_nat_recl; last by ins.
  by rewrite mem_cat; apply/orP; left.
Qed.

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

Lemma mem_bigcat_ord:
  forall (T: eqType) x n (j: 'I_n) (f: 'I_n -> list T)
         (LE: j < n) (IN: x \in (f j)),
    x \in \cat_(i < n) (f i).
Proof.
  ins; rewrite (big_mkord_ord nil).
  rewrite -(big_mkord (fun x => true)).
  apply mem_bigcat_nat with (j := j);
    [by apply/andP; split | by rewrite eq_fun_ord_to_nat].
Qed.

Lemma strong_ind :
  forall (P: nat -> Prop),
    P 0 -> (forall n, (forall k, k <= n -> P k) -> P n.+1) ->
    forall n, P n.
Proof.
  intros P P0 ALL; destruct n; first by apply P0.
  apply ALL;  generalize dependent n; induction n.
    by intros k LE0; move: LE0; rewrite leqn0; move => /eqP LE0; subst k.
    intros k LESn; destruct (ltngtP k n.+1) as [LT | GT | EQ].
      by rewrite ltnS in LT; apply IHn.
      by rewrite leqNgt GT in LESn.
      by rewrite EQ; apply ALL, IHn.
Qed.
  
Lemma exists_inP_nat t (P: nat -> bool):
  reflect (exists x, x < t /\ P x) [exists (x | x \in 'I_t), P x].
Proof.
  destruct [exists x0 in 'I_t, P x0] eqn:EX; [apply ReflectT | apply ReflectF]; ins.
    move: EX => /exists_inP EX; des.
    by exists x; split; [by apply ltn_ord |].

    apply negbT in EX; rewrite negb_exists_in in EX.
    move: EX => /forall_inP ALL.
    unfold not; ins; des.
    specialize (ALL (Ordinal H)).
    by exploit ALL; unfold negb; try rewrite H0.
Qed.

Lemma forall_inP_nat (t: nat) (P: nat -> bool):
  reflect ((forall (x: nat) (LT: x < t), P x)) [forall (x | x \in 'I_t), P x].
Proof.
  destruct [forall x0 in 'I_t, P x0] eqn:ALL; [apply ReflectT | apply ReflectF]; ins.
    move: ALL => /forall_inP ALL; des.
    by exploit (ALL (Ordinal LT)). 

    apply negbT in ALL; rewrite negb_forall_in in ALL.
    move: ALL => /exists_inP ALL; des.
    unfold not; ins; des.
    by exploit (H x); [by apply ltn_ord | by apply/negP].
Qed.

Lemma exists_inPQ_nat t (P Q: nat -> bool):
  reflect (exists x, x < t /\ P x /\ Q x) [exists (x | x \in 'I_t), P x && Q x].
Proof.
  destruct [exists x0 in 'I_t, P x0 && Q x0] eqn:EX; [apply ReflectT | apply ReflectF]; ins.
    move: EX => /exists_inP EX; des.
    move: H2 => /andP H2; des.
    by exists x; split; [by apply ltn_ord |].

    apply negbT in EX; rewrite negb_exists_in in EX.
    move: EX => /forall_inP ALL.
    unfold not; ins; des.
    specialize (ALL (Ordinal H)).
    by exploit ALL; unfold negb; try rewrite H0 H1.
Qed.

Lemma subh1 : forall m n p (GE: m >= n), m - n + p = m + p - n.
Proof.
  by ins; ssromega.
Qed.

Lemma subh2 : forall m1 m2 n1 n2 (GE1: m1 >= m2) (GE2: n1 >= n2),
  (m1 + n1) - (m2 + n2) = m1 - m2 + (n1 - n2).
Proof.
  by ins; ssromega.
Qed.

Lemma subh3 : forall m n p (GE1: m + p <= n) (GE: n >= p),
                    (m <= n - p).
Proof.
  ins. rewrite <- leq_add2r with (p := p).
  by rewrite subh1 // -addnBA // subnn addn0.
Qed.

Lemma subh4: forall m n p (LE1: m <= n) (LE2: p <= n),
             (m == n - p) = (p == n - m).
  intros.
  apply/eqP.
  destruct (p == n - m) eqn:EQ.
    by move: EQ => /eqP EQ; rewrite EQ subKn.
    by apply negbT in EQ; unfold not; intro BUG;
      rewrite BUG subKn ?eq_refl in EQ.
Qed.

Lemma ltn_div_trunc :
  forall m n d (NONZERO: d > 0) (DIV: m %/ d < n %/ d), m < n.
Proof.
  ins.
  rewrite ltn_divLR in DIV; last by ins.
  by apply leq_trans with (n := n %/ d * d);
    [by ins| by apply leq_trunc_div].
Qed.
  
Lemma addmovr: forall m n p (GE: m >= n), m - n = p <-> m = p + n.
Proof.
  split; ins; ssromega.
Qed.

Lemma addmovl: forall m n p (GE: m >= n), p = m - n <-> p + n = m.
Proof.
  split; ins; ssromega.
Qed.

Lemma subndiv_eq_mod: forall n d, n - n %/ d * d = n %% d.
Proof.
  by ins; rewrite {1}(divn_eq n d) addnC -addnBA // subnn addn0.
Qed.

Lemma sum_diff_monotonic :
  forall n G F (ALL: forall i : nat, i < n -> G i <= F i),
    (\sum_(0 <= i < n) (G i)) <= (\sum_(0 <= i < n) (F i)).
Proof.
  ins; rewrite big_nat_cond [\sum_(0 <= i < n) F i]big_nat_cond.
  apply leq_sum; intros i LT; rewrite andbT in LT.
  move: LT => /andP LT; des.
  apply ALL, leq_trans with (n := n); ins.
Qed.

Lemma sum_diff : forall n F G (ALL: forall i (LT: i < n), F i >= G i),
    \sum_(0 <= i < n) (F i - G i) =
    (\sum_(0 <= i < n) (F i)) -
    (\sum_(0 <= i < n) (G i)).       
Proof.
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
  forall (T: Type) (F: T->nat) r (x0: T)
  (ALL: forall i, i < (size r).-1 -> F (nth x0 r i) <= F (nth x0 r i.+1))
  i k (LT: i + k <= (size r).-1),
    F (nth x0 r i) <= F (nth x0 r (i+k)).
Proof.
  intros.
  generalize dependent i. generalize dependent k.
  induction k; intros; first by rewrite addn0 leqnn.
  specialize (IHk i.+1); exploit IHk; [by rewrite addSnnS | intro LE].
  apply leq_trans with (n := F (nth x0 r (i.+1))); last by rewrite -addSnnS.
  apply ALL, leq_trans with (n := i + k.+1); last by ins.
  by rewrite addnS ltnS leq_addr.
Qed.

Lemma telescoping_sum :
  forall (T: Type) (F: T->nat) r (x0: T)
  (ALL: forall i, i < (size r).-1 -> F (nth x0 r i) <= F (nth x0 r i.+1)), 
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

Definition make_sequence {T: Type} (opt: option T) :=
  match opt with
    | Some j => [:: j]
    | None => [::]
  end.

Lemma ltSnm : forall n m, n.+1 < m -> n < m.
Proof.
  by ins; apply ltn_trans with (n := n.+1); [by apply ltnSn |by ins].
Qed.

Lemma iter_fix T (F : T -> T) x k n :
  iter k F x = iter k.+1 F x -> k <= n -> iter n F x = iter n.+1 F x.
Proof.
  move => e. elim: n. rewrite leqn0. by move/eqP<-.
  move => n IH. rewrite leq_eqVlt; case/orP; first by move/eqP<-.
  move/IH => /= IHe. by rewrite -!IHe.
Qed.

Lemma fun_monotonic_iter_monotonic :
  forall k f x0
         (MON: forall x1 x2, x1 <= x2 -> f x1  <= f x2)
         (GE0: f 0 >= x0),
    iter k f x0 <= iter k.+1 f x0.
Proof.
  induction k; ins.
    by apply leq_trans with (n := f 0); [by ins | by apply MON].
    by apply MON, IHk; ins.
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

Lemma divSn_cases :
  forall n d (GT1: d > 1),
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

Definition antisymmetric_over_seq {T: eqType} (leT: rel T) (s: seq T) :=
  forall x y (INx: x \in s) (INy: y \in s)
             (LEx: leT x y) (LEy: leT y x),
    x = y.

Lemma before_ij_implies_leq_ij :
  forall {T: eqType} (s: seq T) (leT: rel T)
         (SORT: sorted leT s) (REFL: reflexive leT)
         (TRANS: transitive leT)
         (i j: 'I_(size s)) (LE: i <= j),
         leT (tnth (in_tuple s) i) (tnth (in_tuple s) j).
Proof.
  destruct i as [i Hi], j as [j Hj]; ins.
  destruct s; first by exfalso; rewrite ltn0 in Hi.
  rewrite 2!(tnth_nth s) /=.
  move: SORT => /pathP SORT.
  assert (EQ: j = i + (j - i)); first by rewrite subnKC.
  remember (j - i) as delta; rewrite EQ; rewrite EQ in LE Hj.
  clear EQ Heqdelta LE.
  induction delta; first by rewrite addn0; apply REFL.
  {
    unfold transitive in *.
    apply TRANS with (y := (nth s (s :: s0) (i + delta))).
    {
      apply IHdelta.
      apply ltn_trans with (n := i + delta.+1); last by apply Hj.
      by rewrite ltn_add2l ltnSn.
    }
    {
      rewrite -addn1 addnA addn1.
      rewrite -nth_behead /=.
      by apply SORT, leq_trans with (n := i + delta.+1);
        [ rewrite ltn_add2l ltnSn | by ins].
    }
  }
Qed.

Lemma leq_ij_implies_before_ij :
  forall {T: eqType} (s: seq T) (leT: rel T)
         (SORT: sorted leT s)
         (REFL: reflexive leT)
         (TRANS: transitive leT)
         (ANTI: antisymmetric_over_seq leT s)
         (i j: 'I_(size s)) (UNIQ: uniq s)
         (REL: leT (tnth (in_tuple s) i) (tnth (in_tuple s) j)),
           i <= j.
Proof.
  ins; destruct i as [i Hi], j as [j Hj]; simpl.
  destruct s; [by clear REL; rewrite ltn0 in Hi | simpl in SORT].
  destruct (leqP i j) as [| LT]; first by ins.
  assert (EQ: i = j + (i - j)).
    by rewrite subnKC; [by ins | apply ltnW].
  unfold antisymmetric_over_seq in *.
  assert (REL': leT (tnth (in_tuple (s :: s0)) (Ordinal Hj)) (tnth (in_tuple (s :: s0)) (Ordinal Hi))).
    by apply before_ij_implies_leq_ij; try by ins; apply ltnW.
  apply ANTI in REL'; try (by ins); try apply mem_tnth.
  move: REL'; rewrite 2!(tnth_nth s) /=; move/eqP.
  rewrite nth_uniq //; move => /eqP REL'.
  by subst; rewrite ltnn in LT.
Qed.

Definition ext_tuple_to_fun_index {T} {ts: seq T} {idx: 'I_(size ts)} (hp: idx.-tuple nat) : 'I_(size ts) -> nat.
  intros tsk; destruct (tsk < idx) eqn:LT.
    by apply (tnth hp (Ordinal LT)).
    by apply 0.
Defined.

Definition extend_ord {max} (y: 'I_max) (x: 'I_y) :=
  Ordinal (ltn_trans (ltn_ord x) (ltn_ord y)).

Lemma eq_ext_tuple_to_fun_index :
  forall {T: Type} {ts: seq T} {idx: 'I_(size ts)} (tp: idx.-tuple nat) (x: 'I_idx),
    (ext_tuple_to_fun_index tp) (extend_ord idx x) = tnth tp x.
Proof.
  ins; unfold ext_tuple_to_fun_index.
  des_eqrefl2; first by f_equal; apply ord_inj.
  {
    move: EQ => /negP EQ; exfalso; apply EQ.
    by simpl; apply ltn_ord.
  }
Qed.

(*Program Definition fun_ord_to_nat2 {n} {T} (x0: T) (f: 'I_n -> T)
        (x : nat) : T :=
  match (x < n) with
      true => (f _)
    | false => x0
  end.
Next Obligation.
  eby eapply Ordinal, Logic.eq_sym.
Defined.

Lemma eq_fun_ord_to_nat2 :
  forall n {T: Type} x0 (f: 'I_n -> T) (x: 'I_n),
    (fun_ord_to_nat2 x0 f) x = f x.
Proof.
  ins. unfold fun_ord_to_nat2.
  des_eqrefl.
    by f_equal; apply ord_inj.
    by destruct x; ins; rewrite i in EQ.
Qed.

(* For all x: 'I_n (i.e., x < n), the conversion preserves equality. *)
Program Definition eq_fun_ord_to_nat :
  forall n {T: Type} x0 (f: 'I_n -> T) (x: 'I_n),
    (fun_ord_to_nat x0 f) x = f x :=
  fun n T x0 f x =>
    match ltn_ord x in eq _ b return
          ( 
            (if b as b' return b = b' -> T then
               fun (H : b = true) => f (@Ordinal n x ( H))
             else fun _ => x0) Logic.eq_refl = f x
          )
          -> fun_ord_to_nat x0 f x = f x
    with
      | Logic.eq_refl => _
    end (Logic.eq_refl (f x)).
Next Obligation.
  destruct x; simpl.
  f_equal; f_equal.
  exact: bool_irrelevance.
Qed.*)
