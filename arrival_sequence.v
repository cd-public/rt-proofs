Require Import Vbase job task util_lemmas
               ssreflect ssrbool eqtype ssrnat seq fintype bigop.

(* Definitions and properties of job arrival sequences. *)
Module ArrivalSequence.

  (* Let time be the set of natural numbers. *)
  Definition time := nat.

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

    (* Whether a job arrives in a particular sequence at time t *)
    Definition arrives_at (j: Job) (arr_seq: arrival_sequence Job) (t: time) :=
      j \in arr_seq t.

    (* A job j of type (JobIn arr_seq) is a job that arrives at some particular
       time in arr_seq. It holds the arrival time and a proof of arrival. *)
    Record JobIn (arr_seq: arrival_sequence Job) : Type :=
    {
      _job_in: Job;
      _arrival_time: time; (* arrival time *)
      _: arrives_at _job_in arr_seq _arrival_time (* proof of arrival *)
    }.

    (* Define a coercion that states that every JobIn is a Job. *)
    Coercion JobIn_is_Job {arr_seq: arrival_sequence Job} (j: JobIn arr_seq) :=
      _job_in arr_seq j.

    (* Define job arrival time as that time that the job arrives (only works for JobIn). *)
    Definition job_arrival {arr_seq: arrival_sequence Job} (j: JobIn arr_seq) :=
      _arrival_time arr_seq j.

    (* Finally, we assume a decidable equality for JobIn, to make it compatible
       with ssreflect. TODO: Is there a better way to do this? *)
    Definition jobin_eqdef (arr_seq: arrival_sequence Job) :=
      (fun j1 j2: JobIn arr_seq => (JobIn_is_Job j1) == (JobIn_is_Job j2)).
    Axiom eqn_jobin : forall arr_seq, Equality.axiom (jobin_eqdef arr_seq).
    Canonical jobin_eqMixin arr_seq := EqMixin (eqn_jobin arr_seq).
    Canonical jobin_eqType arr_seq := Eval hnf in EqType (JobIn arr_seq) (jobin_eqMixin arr_seq).

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
    Definition has_arrived (t: nat) := job_arrival j <= t.

    (* A job arrived before t iff it arrives at some time t_0, with 0 <= t_0 < t. *)
    Definition arrived_before (t: nat) := job_arrival j < t.

    (* A job arrives between t1 and t2 iff it arrives at some time t with t1 <= t < t2. *)
    Definition arrived_between (t1 t2: nat) := t1 <= job_arrival j < t2.

  End ArrivingJobs.

End ArrivalSequence.
