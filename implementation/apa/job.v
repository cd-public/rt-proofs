Require Import rt.model.time rt.util.all.
Require Import rt.implementation.apa.task.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.

Module ConcreteJob.

  Import Time.
  Import ConcreteTask.

  Section Defs.

    Context {num_cpus: nat}.
    
    (* Definition of a concrete task. *)
    Record concrete_job :=
    {
      job_id: nat;
      job_cost: time;
      job_deadline: time;
      job_task: @concrete_task num_cpus
    }.

    (* To make it compatible with ssreflect, we define a decidable
       equality for concrete jobs. *)
    Definition job_eqdef (j1 j2: concrete_job) :=
      (job_id j1 == job_id j2) &&
      (job_cost j1 == job_cost j2) &&
      (job_deadline j1 == job_deadline j2) &&
      (job_task j1 == job_task j2).

    (* Next, we prove that job_eqdef is indeed an equality, ... *)
    Lemma eqn_job : Equality.axiom job_eqdef.
    Proof.
      unfold Equality.axiom; intros x y.
      destruct (job_eqdef x y) eqn:EQ.
      {
        apply ReflectT; unfold job_eqdef in *.
        move: EQ => /andP [/andP [/andP [/eqP ID /eqP COST] /eqP DL] /eqP TASK].
        by destruct x, y; simpl in *; subst.
      }
      {
        apply ReflectF.
        unfold job_eqdef, not in *; intro BUG.
        apply negbT in EQ; rewrite negb_and in EQ.
        destruct x, y.
        rewrite negb_and in EQ.
        move: EQ => /orP [EQ | /eqP TASK]; last by apply TASK; inversion BUG.
        move: EQ => /orP [EQ | /eqP DL].
        rewrite negb_and in EQ.
        move: EQ => /orP [/eqP ID | /eqP COST].
        by apply ID; inversion BUG.
        by apply COST; inversion BUG.
        by apply DL; inversion BUG.
      }
    Qed.

    (* ..., which allows instantiating the canonical structure. *)
    Canonical concrete_job_eqMixin := EqMixin eqn_job.
    Canonical concrete_job_eqType := Eval hnf in EqType concrete_job concrete_job_eqMixin.

   End Defs.
    
End ConcreteJob.