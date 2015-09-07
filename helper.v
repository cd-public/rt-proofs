Require Import Vbase ssreflect ssrbool eqtype ssrnat seq fintype bigop ssromega.

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

Lemma addmovr: forall m n p (GE: m >= n), m - n = p <-> m = p + n.
Proof.
  split; ins; ssromega.
Qed.

Lemma addmovl: forall m n p (GE: m >= n), p = m - n <-> p + n = m.
Proof.
  split; ins; ssromega.
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
