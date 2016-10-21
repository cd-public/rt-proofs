Require Import rt.util.all rt.model.arrival.basic.task rt.model.time.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.

(* Definitions and properties of job arrival sequences. *)
Module ArrivalSequence.

  Export Time.
  
  (* Next, we define a job arrival sequence (can be infinite). *)
  Section ArrivalSequenceDef.

    (* Given any job type with decidable equality, ... *)
    Variable Job: eqType.

    (* ..., an arrival sequence is a mapping from time to a sequence of jobs. *)
    Definition arrival_sequence := time -> seq Job.

  End ArrivalSequenceDef.

  (* Note that Job denotes the universe of all possible jobs.
     In order to distinguish jobs of different arrival sequences, next we
     define a subtype of Job called JobIn. *)
  Section JobInArrivalSequence.

    Context {Job: eqType}.

    (* First we define whether a job arrives in a particular sequence at time t. *)
    Definition arrives_at (j: Job) (arr_seq: arrival_sequence Job) (t: time) :=
      j \in arr_seq t.

    (* Next, we define the type (JobIn arr_seq) to represent a job that belongs to arr_seq.
       (Note: The notation might seem complicated, but it just means that the type JobIn is
              constructed using a Job j, a time t, and a proof of arrival. *)
    Inductive JobIn (arr_seq: arrival_sequence Job) :=
      Build_JobIn j t of (arrives_at j arr_seq t).

    (* Next, we define a coercion that returns the Job contained in the type JobIn. *)
    Coercion job_of_job_in {arr_seq} (j: JobIn arr_seq) : Job :=
      let: Build_JobIn actual_job _ _ := j in actual_job.

    (* Similarly, we define a function that returns the arrival time of the job. *)
    Definition job_arrival {arr_seq: arrival_sequence Job} (j: JobIn arr_seq) :=
      let: Build_JobIn _ arr _ := j in arr.

    (* Finally, we define a decidable equality for JobIn, in order to make
       it compatible with ssreflect (see jobin_eqdec.v). *)
    Load jobin_eqdec.

  End JobInArrivalSequence.

  (* A valid arrival sequence must satisfy some properties. *)
  Section ArrivalSequenceProperties.

    Context {Job: eqType}.
    Variable arr_seq: arrival_sequence Job.

    (* The same job j cannot arrive at two different times. *)
    Definition no_multiple_arrivals :=
      forall (j: Job) t1 t2,
        arrives_at j arr_seq t1 -> arrives_at j arr_seq t2 -> t1 = t2.

    (* The sequence of arrivals at a particular time has no duplicates. *)
    Definition arrival_sequence_is_a_set := forall t, uniq (arr_seq t).

  End ArrivalSequenceProperties.

  (* Next, we define whether a job has arrived in an interval. *)
  Section ArrivingJobs.

    Context {Job: eqType}.
    Context {arr_seq: arrival_sequence Job}.
    Variable j: JobIn arr_seq.

    (* A job has arrived at time t iff it arrives at some time t_0, with 0 <= t_0 <= t. *)
    Definition has_arrived (t: time) := job_arrival j <= t.

    (* A job arrived before t iff it arrives at some time t_0, with 0 <= t_0 < t. *)
    Definition arrived_before (t: time) := job_arrival j < t.

    (* A job arrives between t1 and t2 iff it arrives at some time t with t1 <= t < t2. *)
    Definition arrived_between (t1 t2: time) := t1 <= job_arrival j < t2.

  End ArrivingJobs.

  (* In this section, we define prefixes of arrival sequences based on JobIn.
     This is not required in the main proofs, but important for instantiating
     a concrete schedule. Feel free to skip this section. *)
  Section ArrivalSequencePrefix.

    Context {Job: eqType}.
    Variable arr_seq: arrival_sequence Job.

    (* Let's define a function that takes a job j and converts it to
       Some JobIn (if j arrives at time t), or None otherwise. *)
    Program Definition is_JobIn (t: time) (j: Job) :=
      if (j \in arr_seq t) is true then
        Some (Build_JobIn arr_seq j t _)
      else None.

    (* Now we define the list of every JobIn that arrives at time t as the partial
       map of is_JobIn.  *)
    Definition jobs_arriving_at (t: time) := pmap (is_JobIn t) (arr_seq t).

    (* By concatenation, we can construct the list of every JobIn that arrived before t2. *)
    Definition jobs_arrived_before (t2: time) :=
      \cat_(t < t2) jobs_arriving_at t.

    (* Based on that, we define the list of every JobIn that has arrived up to time t2, ... *)
    Definition jobs_arrived_up_to (t2: time) :=
      jobs_arrived_before t2.+1.

    (* ...and the list of every JobIn that arrived in the interval [t1, t2). *)
    Definition jobs_arrived_between (t1 t2: time) :=
      [seq j <- jobs_arrived_before t2 | job_arrival j >= t1].

    Section Lemmas.
      
      (* There's an inverse function for recovering the original Job from JobIn. *)
      Lemma is_JobIn_inverse :
        forall t,
          ocancel (is_JobIn t) job_of_job_in.
      Proof.
        by intros t; red; intros x; unfold is_JobIn; des_eqrefl.
      Qed.

      (* Prove that a member of the list indeed satisfies the property. *)
      Lemma JobIn_arrived:
        forall j t,
          j \in jobs_arrived_before t <-> arrived_before j t.
      Proof.
        intros j t; split.
        {
          intros IN; apply mem_bigcat_ord_exists in IN; destruct IN as [t0 IN].
          unfold jobs_arriving_at in IN.
          rewrite mem_pmap in IN.
          move: IN => /mapP [j' IN SOME].
          unfold is_JobIn in SOME.
          des_eqrefl; last by done.
          inversion SOME; subst.
          unfold has_arrived; simpl.
          by apply ltn_ord.
        }
        {
          unfold has_arrived; intros ARRIVED.
          apply mem_bigcat_ord with (j := Ordinal ARRIVED); first by done.
          rewrite mem_pmap; apply/mapP; exists j;
            first by destruct j as [j arr_j ARR].
          destruct j as [j arr_j ARR].
          unfold is_JobIn; des_eqrefl; first by repeat f_equal; apply bool_irrelevance.
          by simpl in *; unfold arrives_at in *; rewrite ARR in EQ.
        }
      Qed.

      (* If the arrival sequence doesn't allow duplicates,
         the same applies for the list of JobIn that arrive. *)
      Lemma JobIn_uniq :
        arrival_sequence_is_a_set arr_seq ->
        forall t, uniq (jobs_arrived_before t).
      Proof.
        unfold jobs_arrived_up_to; intros SET t.
        apply bigcat_ord_uniq.
        {
          intros i; unfold jobs_arriving_at.
          apply pmap_uniq with (g := job_of_job_in); first by apply is_JobIn_inverse.
          by apply SET.
        }
        {
          intros x t1 t2 IN1 IN2.
          rewrite 2!mem_pmap in IN1 IN2.
          move: IN1 IN2 => /mapP IN1 /mapP IN2.
          destruct IN1 as [j1 IN1 SOME1], IN2 as [j2 IN2 SOME2].
          unfold is_JobIn in SOME1; des_eqrefl; last by done.
          unfold is_JobIn in SOME2; des_eqrefl; last by done.
          by rewrite SOME1 in SOME2; inversion SOME2; apply ord_inj.
        }
      Qed.
      
    End Lemmas.
    
  End ArrivalSequencePrefix.

End ArrivalSequence.