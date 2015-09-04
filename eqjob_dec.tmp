(* Assume decidable equality for jobs, so that it can be
   used in computations. *)

Require Import eqtype.

Parameter job_eq_dec: job -> job -> bool.
Axiom eqn_job : Equality.axiom job_eq_dec.

Canonical job_eqMixin := EqMixin eqn_job.
Canonical job_eqType := Eval hnf in EqType job job_eqMixin.


(*(* Define decidable equality for jobs, so that it can be
   used in computations. *)
Definition job_eq_dec (x y: job) : {x = y} + {x <> y}.
  destruct x, y;
  destruct (eq_op job_id0 job_id1) eqn: Eid;
  destruct (eq_op job_arrival0 job_arrival1) eqn:Earrival;
  destruct (eq_op job_cost0 job_cost1) eqn:Ecost;
  destruct (eq_op job_deadline0 job_deadline1) eqn:Edeadline;
  move: Eid Earrival Ecost Edeadline => /eqP Eid /eqP Earrival /eqP Ecost /eqP Edeadline;
  des; subst;
  try (by left; ins);
  try (by right; unfold not; intro EQ; inversion EQ; intuition).
Qed.

(* ssreflect decidable equality *)
  Lemma eqn_job : Equality.axiom job_eq_dec.
  Proof.
    unfold Equality.axiom; ins; destruct (job_eq_dec x y);
    [by apply ReflectT | by apply ReflectF].  
  Qed.

  Canonical job_eqMixin := EqMixin eqn_job.
  Canonical job_eqType := Eval hnf in EqType job job_eqMixin.
(* ---------------------------- *)*)