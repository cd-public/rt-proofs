Require Import rt.util.all.
Require Import rt.model.time rt.model.arrival.basic.job rt.model.arrival.basic.arrival_sequence rt.model.priority.
Require Import rt.model.schedule.uni.schedule rt.model.schedule.uni.workload.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.

Module Swap.

  Import UniprocessorSchedule.

  (* In this section we define a function that swaps two jobs
     in a schedule. *)
  Section Defs.

    Context {Job: eqType}.
	
    (* Consider any schedule of jobs. *)
    Variable sched: schedule Job.

    (* Let t1 and t2 be any points in time. *)
    Variable t1 t2: time.

    (* For simplicity, define some local variables. *)
    Let job_at_t1 := sched t1.
    Let job_at_t2 := sched t2.

    (* We define swap as a new schedule in which whatever is scheduled
       at times t1 and t2 in the original schedule are swapped. *)
    Definition swap :=
      fun (t:time) =>
        if t == t2 then
          job_at_t1
        else if t == t1 then
          job_at_t2
        else sched t.

  End Defs.

  (* In this section we prove lemmas about the swap function. *)
  Section Lemmas.
    Context {Job: eqType}.

    (* Consider any schedule of jobs. *)
    Variable sched: schedule Job.

    (* In this section we prove symmetry properties of swap. *)
    Section Symmetry.

      (* Let t1 and t2 be any time instants to be swapped. *)
      Variable t1 t2: time.

      (* For simplicity, define some local variables. *)
      Let new_sched := swap sched t1 t2.

      (* First, we prove that the swap function is commutative with regard to times t1 and t2 ... *)
      Lemma swap_commutative:
        forall t, swap sched t2 t1 t = swap sched t1 t2 t.
      Proof.
        Admitted.

      (* ...which implies that the service function is also commutative. *)
      Corollary swap_service_commutative:
        forall j t,
          service (swap sched t2 t1) j t = service (swap sched t1 t2) j t.
      Proof.
        Admitted.

      (* If the two swap slots are the same, the schedule stays the same. *)
      Lemma swap_same_schedule_for_same_time :
	    forall t, t1 = t2 -> new_sched t = sched t.
      Proof.
        Admitted.

    End Symmetry.

    (* In this section we prove some lemmas about the service of jobs
       before the times that are swapped. *)
    Section TimeInstantsBeforeSwap.

      (* Let t1 and t2 any points *)
      Variable t1 t2: time.

      (* For simplicity, define some local variables. *)
      Let new_sched := swap sched t1 t2.

      (* ...and let j be any job.*)
      Variable j : Job.

      (* At any point in time different from the time that are swapped
         new_sched is the same as the original one. *)
      Lemma schedules_invariant_elsewhere_t1_and_t2:
        forall t, t <> t1 ->
                  t <> t2 ->
                  new_sched t = sched t.
      Proof.
        Admitted.

      (* Consequently the service of j in new_sched will be the same
         as in the original schedule. *)
      Corollary service_invariant_before_t1_and_t2:
        forall t, t <= t1 -> t <= t2 -> service new_sched j t = service sched j t.
      Proof.
        Admitted.
      
    End TimeInstantsBeforeSwap.

    Section TimeInstantsAfterSwap.

      (* Let t1 and t2 any points in time. *)
      Variable t1 t2: time.

      (* For simplicity, define some local variables. *)
      Let new_sched := swap sched t1 t2.

      (*Let t be any point in time after t1 and t2 ... *)
      Variable j : Job.
      Variable t : time.
      Hypothesis H_after_t1: t1 < t.
      Hypothesis H_after_t2: t2 < t.

      (* ... then the service of j in new_sched will be the same
             as in the original schedule. *)
      Lemma service_invariant_after_t1_and_t2:
        service new_sched j t = service sched j t.
      Proof.
        Admitted.

    End TimeInstantsAfterSwap.

    Section JobsNotInvolvedInSwap.

      (* Let t1 and t2 any points in time. *)
      Variable t1 t2: time.

      (* For simplicity, define some local variables. *)
      Let new_sched := swap sched t1 t2.
      
      (* Let j be any job that is neither scheduled at times t1 nor t2. *)
      Variable j : Job.
      Hypothesis H_not_scheduled_at_t1: scheduled_at sched j t1.
      Hypothesis H_not_scheduled_at_t2: scheduled_at sched j t2.

      (* If a job is neither scheduled at t1 nor at t2, the service for this job does not change. *)
      Lemma service_invariant_not_involved_job:
        forall t, service new_sched j t = service sched j t.
      Proof.
        Admitted.

    End JobsNotInvolvedInSwap.

  End Lemmas.
  
End Swap.