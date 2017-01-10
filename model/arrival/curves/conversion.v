Require Import Coq.Logic.ConstructiveEpsilon.
Require Import rt.util.all.
Require Import rt.model.arrival.basic.arrival_sequence.
Require Import rt.model.arrival.curves.bounds.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq div.

(* In this section, we show how to convert between arrival bounds and separation bounds. *)
Module ArrivalConversion.

  Import ArrivalSequence ArrivalCurves.

  (* For simplicity, we redefine some names. *)
  Definition linear_search := constructive_indefinite_ground_description_nat.
  
  (* Next, we show how to perform the conversion. *)
  Section Conversion.

    Context {Task: eqType}.
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_task: Job -> Task.

    (* Consider any job arrival sequence ...*)
    Variable arr_seq: arrival_sequence Job.
    
    (* ...and let tsk be any task to be analyzed. *)
    Variable tsk: Task.
    
    (* First, we convert an arrival bound into a separation bound. *)
    Section ArrivalToSeparation.

      (* Let max_arrivals be any arrival bound of tsk. *)
      Variable max_arrivals: time -> nat.
      Hypothesis H_is_arrival_bound:
        is_arrival_bound job_task arr_seq tsk max_arrivals.

      (* Assume that jobs of each task arrive infinitely often. *)
      Hypothesis H_jobs_arrive_infinitely_often:
        forall j1,
          exists j2,
            job_task j1 = job_task j2 /\
            job_arrival j1 <= job_arrival j2.
      
      (* Next, given any number of job arrivals, we show how to compute the minimum interval
         length that can contain all these arrivals.
         The computation is done using a linear search for larger values. *)
      Section ComputingSeparationBound.
        
        (* Consider any number of job arrivals. *)
        Variable num_arrivals: time.
      
        (* Then, we define a predicate that checks whether an interval delta is a separation
           bound for this number of arrivals, ... *)
        Definition contains_all_arrivals (delta: nat) :=
          max_arrivals delta >= num_arrivals.

        (* ...which we prove to be decidable (since it is a boolean). *)
        Lemma contains_all_arrivals_decidable:
          forall delta, {contains_all_arrivals delta} + {~ contains_all_arrivals delta}.
        Proof.
          by intros delta; apply Bool.bool_dec.
        Qed.

        (* Next, using the fact that jobs arrive infinitely often, we show that there always
           exist an interval delta that contains this number of arrivals, ...*)
        Lemma interval_exists:
          exists delta, contains_all_arrivals delta.
        Proof.
        Admitted.

        (* ...we run a linear search that looks for this delta. This returns
           a value delta and a proof that delta contains all the arrivals. *)
        Definition find_delta := linear_search contains_all_arrivals
                                               contains_all_arrivals_decidable
                                               interval_exists.

        (* Next, we prove that this linear serch finds the minimum element that
           satisfies the property.
           (TODO: This proof is optional, just for tightness.
                  Also, it might require dealing with ConstructiveEpsilon). *)
        Lemma find_delta_returns_min: true.
        Admitted.
        
        (* To conclude, we define the conversion from arrival bound to separation bound
           as this number returned by the linear search. *)
        Definition convert_to_separation_bound := proj1_sig find_delta.

      End ComputingSeparationBound.
      
      (* Based on the computation above, we prove that any value that is returned is indeed
         a separation bound. *)
      Lemma conversion_to_separation_bound_is_valid:
        is_separation_bound job_task arr_seq tsk convert_to_separation_bound.
      Proof.
        intros t1 t2 LE.
      Admitted.
      
    End ArrivalToSeparation.

    (* Next, we convert a separation bound into an arrival bound. *)
    Section SeparationToArrival.

      (* Let min_length be any separation bound of tsk. *)
      Variable min_length: nat -> time.
      Hypothesis H_is_separation_bound:
        is_separation_bound job_task arr_seq tsk min_length.

      (* Then, by computing xxxxxx, ...*)
      Definition convert_to_arrival_bound (k: time) := 0. (* TODO: FIX *)
      
      (* ...we transform min_length to obtain an arrival bound. *)
      Lemma conversion_to_upper_curve_succeeds:
        is_arrival_bound job_task arr_seq tsk convert_to_arrival_bound.
      Proof.
      Admitted.

    End SeparationToArrival.
    
  End Conversion.

End ArrivalConversion.