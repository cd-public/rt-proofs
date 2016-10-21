Require Import rt.util.all rt.model.arrival.basic.arrival_sequence.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.

(* In this file we provide extra definitions for job arrival sequences with jitter. *)
Module ArrivalSequenceWithJitter.

  Export ArrivalSequence.
  
  (* First, we identify the actual arrival time of a job. *)
  Section ActualArrival.

    Context {Job: eqType}.
    Variable job_jitter: Job -> time.

    (* Let j be any job in the arrival sequence. *)
    Context {arr_seq: arrival_sequence Job}.
    Variable j: JobIn arr_seq.

    (* We define the actual arrival of job j as the time when the jitter ends. *)
    Definition actual_arrival := job_arrival j + job_jitter j.

    (* Next, we state whether the actual arrival of job j occurs in some interval [0, t], ... *)
    Definition jitter_has_passed (t: time) := actual_arrival <= t.

    (* ...along with the variants for interval [0, t), ... *)
    Definition actual_arrival_before (t: time) := actual_arrival < t.

    (* ...and interval [t1, t2). *)
    Definition actual_arrival_between (t1 t2: time) :=
      t1 <= actual_arrival < t2.

  End ActualArrival.

  (* In this section, we show how to compute the list of arriving jobs. *)
  Section ArrivingJobs.

    Context {Job: eqType}.
    Variable job_jitter: Job -> time.
    Variable arr_seq: arrival_sequence Job.

    (* First, we define the actual job arrivals (including jitter) in the interval [0, t)... *)
    Definition actual_arrivals_before (t: time) :=
      [seq j <- jobs_arrived_before arr_seq t | actual_arrival job_jitter j < t].

    (* ...and in the interval [0, t]. *)
    Definition actual_arrivals_up_to (t: time) := actual_arrivals_before t.+1.

    (* Similarly, we also define the actual job arrivals in the interval [t1, t2). *)
    Definition actual_arrivals_between (t1 t2: time) :=
      [seq j <- actual_arrivals_before t2 | actual_arrival job_jitter j >= t1].

    Section Lemmas.
      
      (* We prove that jobs are in the list of actual arrivals iff they actually arrived. *)
      Lemma actual_arrivals_arrived:
        forall j t,
          j \in actual_arrivals_before t <-> actual_arrival_before job_jitter j t.
      Proof.
        intros j t; split; first by rewrite mem_filter; move => /andP [LE IN].
        intros ARRIVED.
        rewrite mem_filter; apply/andP; split; first by done.
        apply JobIn_arrived.
        by apply leq_ltn_trans with (n := actual_arrival job_jitter j); first by apply leq_addr.
      Qed.
      
    End Lemmas.
    
  End ArrivingJobs.

End ArrivalSequenceWithJitter.