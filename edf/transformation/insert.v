Require Import rt.util.all.
Require Import rt.model.time rt.model.arrival.basic.job rt.model.arrival.basic.arrival_sequence rt.model.priority.
Require Import rt.model.schedule.uni.schedule rt.model.schedule.uni.workload.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.


Module Insert.

  Import UniprocessorSchedule.

  (* In this section we define the function that inserts a job
     in a schedule. *)

  Section Defs.

    Context {Job: eqType}.

    (* Consider any uniprocessor schedule. *)
    Variable sched: schedule Job.

    (* Let t be any point in time ... *)
    Variable t_insert : time.
    (* ...and j_new be the job to be inserted. *)
    Variable j_new : Job.

    (* The function insert returns a schedule that is the same as
       the original one but with job j_new scheduled at time t. *)
    Definition insert :=
      fun (t:time) => if t_insert == t then Some j_new else sched t.
    
  End Defs.

  (* In this section, we prove lemmas about the insert function. *)
  Section Lemmas.

    Context {Job: eqType}.

    (* Consider any uniprocessor schedule. *)
    Variable sched: schedule Job.

    (* Let t be any point in time ... *)
    Variable t_insert : time.
    (* ...and j_new be the job to be inserted. *)
    Variable j_new : Job.

    (* For simplicity, we define some local names. *)
    Let replaced_job := sched t_insert.
    Let new_sched := insert sched t_insert j_new.

    (* First, we prove some lemmas about the new schedule. *)
    Section Schedule.
      
      (* In the new schedule, job j_new is scheduled at time t. *)
      Lemma insert_changes_job_at_time_t:
        new_sched t_insert = Some j_new.
      Proof.
        Admitted.
      
      (* For any point in time other than t the new schedule
         is the same as the old one. *)
      Lemma insert_same_schedule_at_different_times:
        forall t, t <> t_insert -> sched t = insert sched t_insert j_new t.
      Proof.
        Admitted.

      (* If j_new is already scheduled at time t in sched,
         then new_sched is the same as sched. *)
      Lemma insert_no_change_if_job_already_scheduled:
        forall t, sched t_insert = Some j_new -> sched t = new_sched t.
      Proof.
        Admitted.

      (* If j_new was not scheduled in sched,
         new_sched is different from sched at time t.*)
      Lemma insert_changes_schedule_if_jobs_are_different:
        Some j_new <> sched t_insert -> new_sched t_insert <> sched t_insert.
      Proof.
        Admitted.

    End Schedule.

    (* In this section, we prove lemmas about service_at in new_sched. *)
    Section ServiceAt.
 
      (* Let j be any job. *)
      Variable j : Job.

      (* The service of j at any point in time different from t in
         new_sched is the same as in sched. *)
      Lemma insert_service_at_stays_the_same_at_times_other_than_t:
        forall t, t <> t_insert -> service_at sched j t = service_at new_sched j t.
      Proof.
        Admitted.

      (* As a corollary the service at any point in time before t
         in new_sched is the same as in sched. *)
      Corollary insert_service_at_stays_the_same_before_t:
        forall t, t < t_insert -> service_at sched j t = service_at new_sched j t.
      Proof.
        Admitted.

    End ServiceAt.

    (* In this section, we prove lemmas about the service in new_sched. *)
    Section Service.

      (* Let j be any job from the arrival sequence. *)
      Variable j : Job.

      (* The service of j before t in new_sched is the same as in sched. *)
      Lemma insert_service_invariant_before_t :
        forall t, t <= t_insert -> service new_sched j t = service sched j t.
      Proof.
        Admitted.

      (* The service of the assigned job j_new in the new schedule is
         either the same as in the original schedule (if j_new
         was already scheduled), or it increases by 1. *)
      Lemma insert_service_of_new_job :
        forall t, t < t_insert -> service new_sched j_new t = service sched j_new t + (replaced_job != Some j_new).
      Proof.
        Admitted.
		
      (* In this section, we prove some lemmas about the service
         of the job which was replaced. *)
      Section ReplacedJob.

        (* If j is the job that was replaced, ... *)
        Hypothesis H_j_is_replaced_job:
          replaced_job = Some j.

        (* ...and the inserted job j_new is the same as the replaced one,
              then the service of j in new_sched at any point in time
              after t decreases by 1 compared to the one in sched.*)
        Lemma insert_service_sched_job:
          forall t,
            t > t_insert ->
            (Some j_new != Some j) ->
            1 + service new_sched j t = service sched j t.
      Proof.
        Admitted.

        (* If j_new is the replaced job, the service does not change. *)
        Lemma insert_service_does_not_change_without_replacement:
          forall t,
            (Some j_new = Some j) ->
            service new_sched j t = service sched j t.
      Proof.
        Admitted.

      End ReplacedJob.

    End Service.

  End Lemmas.

End Insert.