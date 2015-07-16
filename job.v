Require Import Vbase task
               eqtype ssrbool ssrnat fintype.

Section Job.

Record job : Type :=
{
  (* UNNEEDED job_id: nat;*) (* job_id allows multiple jobs with same parameters *)
  job_cost: nat; (* actual cost *)
  job_deadline: nat; (* relative deadline *)
  job_task: sporadic_task; (* Task that spawns this job *)

  job_properties:
    << job_cost_positive: job_cost > 0 >> /\
    << job_cost_le_deadline: job_cost <= job_deadline >> /\
    << job_dl_positive: job_deadline > 0 >> /\
    << job_params: (job_cost <= task_cost job_task /\
                    job_deadline = task_deadline job_task)>>
}.

Definition job_of (tsk: sporadic_task) (j: job) : bool :=
  beq_task (job_task j) tsk.

(* Define decidable equality for jobs, so that it can be
   used in computations. *)
Definition job_eq_dec (x y: job) : {x = y} + {x <> y}.
  destruct x, y.
  destruct (eq_op job_cost0 job_cost1) eqn:Ecost;
  destruct (eq_op job_deadline0 job_deadline1) eqn:Edeadline;
  destruct (beq_task job_task0 job_task1) eqn:Etask;
  unfold beq_task in *;
  destruct (task_eq_dec job_task0 job_task1); subst.
Admitted.
(*
  try (by left; apply f_equal, proof_irrelevance);
  try (by right; unfold not; intro EQ; inversion EQ; intuition).
Defined.*)

Definition beq_job (x y: job) := if job_eq_dec x y then true else false.

(* - ssreflect decidable equality -- IGNORE! - *)
  Lemma eqn_job : Equality.axiom beq_job.
  Proof.
    unfold beq_job, Equality.axiom; ins; desf;
    [by apply ReflectT | by apply ReflectF].  
  Qed.

  Canonical job_eqMixin := EqMixin eqn_job.
  Canonical job_eqType := Eval hnf in EqType job job_eqMixin.
(* ----------------------------------------- *)

(* Observations / TODO *)
(* 1) It should be ok to have 0-cost jobs. Deadlines can also be 0,
      as long as the cost is no greater than the deadline.
      But let's keep it like this for now. We can remove the restriction if needed.

   2) job_task could be (option sporadic_task), so that we allow jobs that
      don't belong to any task. But our definition of job is not modular yet,
      so we could leave that for when we support different task models.
      For different task models, we might allow multiple jobs with same parameters,
      but the current specification is ok for the sporadic task model.

   3) job_properties restrict the deadline of the job to have the same
      deadline as the task. Doesn't work for overhead accounting.
      We might want to decouple job_properties from job and enforce them depending
      on the task model.
*)

End Job.