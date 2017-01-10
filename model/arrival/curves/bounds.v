Require Import rt.util.all.
Require Import rt.model.arrival.basic.arrival_sequence
               rt.model.arrival.basic.task_arrival.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq div.

(* In this section, we define the notion of arrival curves, which
   can be used to reason about the frequency of job arrivals. *)
Module ArrivalCurves.

  Import ArrivalSequence TaskArrival.

  Section DefiningArrivalCurves.

    Context {Task: eqType}.
    
    Context {Job: eqType}.
    Variable job_task: Job -> Task.
    
    (* Consider any job arrival sequence... *)
    Variable arr_seq: arrival_sequence Job.

    (* ...and let tsk be any task to be analyzed. *)
    Variable tsk: Task.
    
    (* Recall the job arrivals of tsk in a given interval [t1, t2). *)
    Let arrivals_of_tsk := arrivals_of_task_between job_task arr_seq tsk.
    Let num_arrivals_of_tsk := num_arrivals_of_task job_task arr_seq tsk. 

    (* First, we define what constitutes an arrival bound for task tsk. *)
    Section ArrivalBound.

      (* Let max_arrivals denote any function that takes an interval length and
         returns the associated number of job arrivals of tsk.
         (This corresponds to the eta+ function in the literature.) *)
      Variable max_arrivals: time -> nat.

      (* Then, we say that num_arrivals is an arrival bound iff, for any interval [t1, t2),
         (num_arrivals (t2 - t1)) bounds the number of jobs of tsk that arrive in that interval. *)
      Definition is_arrival_bound :=
        forall t1 t2,
          t1 <= t2 ->
          num_arrivals_of_tsk t1 t2 <= max_arrivals (t2 - t1).

    End ArrivalBound.

    (* Next, we define the notion of a separation bound for task tsk, i.e., the smallest
       interval length in which a certain number of jobs of tsk can be spawned. *)
    Section SeparationBound.

      (* Let min_length denote any function that takes a number of jobs and
         returns an associated interval length.
         (This corresponds to the delta- function in the literature.) *)
      Variable min_length: nat -> time.

      (* Then, we say that min_length is a separation bound iff, for any number of jobs
         of tsk, min_separation lower-bounds the minimum interval length in which that number
         of jobs can be spawned. *)
      Definition is_separation_bound :=
        forall t1 t2,
          t1 <= t2 ->
          min_length (num_arrivals_of_tsk t1 t2) <= t2 - t1.
      
    End SeparationBound.

  End DefiningArrivalCurves.

End ArrivalCurves.