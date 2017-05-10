Require Import rt.util.all.
Require Import rt.model.time rt.model.arrival.basic.job rt.model.arrival.basic.arrival_sequence rt.model.priority.
Require Import rt.model.schedule.uni.schedule rt.model.schedule.uni.workload.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.

Module Erase.

  Import UniprocessorSchedule.
  
  (* In this section we define the erase transformation for uniprocessor schedules. *)
  Section Defs.

    Context {Job: eqType}.

    (* Given any uniprocessor schedule of these jobs. *)
    Variable sched: schedule Job.
    
    (* Let t_erase be the time where a job will be erased. *)
    Variable t_erase: time.
    
    (* Then, we define the erase as the schedule in which
       time t is replaced by an idle time. *)
    Definition erase :=
      fun (t:time) => if t == t_erase then None else sched t.

  End Defs.

  (* In this section we prove some lemmas about the erase transformation. *)
  Section Lemmas.

    Context {Job: eqType}.

    (* Consider any uniprocessor schedule of these jobs. *)
    Variable sched: schedule Job.

    (* Let new_sched be the schedule produced by erasing time t. *)
    Variable t_erase : time.
    Let new_sched := erase sched t_erase.

    (* First, we show that the generated schedule is the same
       at all times other than t_erase. *)
    Lemma erase_same_schedule_at_other_times:
      forall t, (t <> t_erase) -> (new_sched t = sched t).
    Proof.
      Admitted.

    (* Next, we prove lemmas for the case where there's no job to be erased. *)
    Section NothingErased.

      (* Assume that the original schedule is idle at the erase time. *)
      Hypothesis H_nothing_to_erase : sched t_erase = None.

      (* Then, we prove that the generated schedule remains the same. *)
      Lemma erase_none_same_schedule:
        forall t, new_sched t = sched t.
      Proof.
        Admitted.

      (* As a result, the service received by any job also doesn't change. *)
      Lemma erase_none_same_service:
        forall j t,
          service new_sched j t = service sched j t.
      Proof.
        Admitted.
      
    End NothingErased.

    (* Next, we prove some lemmas about the service before the erase time. *)
    Section BeforeEraseTime.

      (* At any time t no later than t_erase, ... *)
      Variable t: time.
      Hypothesis H_no_later_than_t: t <= t_erase.

      (* ...the service received by any job is the same as in the original schedule. *)
      Lemma erase_same_service_before_erase_time:
        forall j, service new_sched j t = service sched j t.
      Proof.
        Admitted.
        
    End BeforeEraseTime.

    (* Next, we prove that the service is preserved for jobs that were not erased. *)
    Section JobWasNotErased.

      (* Let j be any job ...*)
      Variable j: Job.

      (* ...that was not scheduled at time t_erase
            in the original schedule. *)
      Hypothesis H_job_not_erased : sched t_erase <> Some j.

      (* Then, the service of j at time t in the new schedule
         is the same as in the original one. *)
      Lemma erase_same_service_after_erase_time:
        forall t,
          service new_sched j t = service sched j t.
      Proof.
        Admitted.

    End JobWasNotErased.

    (* In this section, we prove some lemmas about the service
       after the erased time. *)
    Section AfterEraseTime.

      (* Let t be any point in time after the erased time. *)
      Variable t_after: time.
      Hypothesis H_after_t: t_after > t_erase.

      (* Now we consider the case when a job is erased. *)
      Section JobWasErased.

        (* Let j be any job that was erased. *)
        Variable j: Job.
        Hypothesis H_job_was_erased: sched t_erase = Some j.

        (* Then, the service received by j after time t
           in the new schedule decreases by one unit. *)
        Lemma erase_service_decreases_after_erase_time:
          service new_sched j t_after = service sched j t_after - 1.
        Proof.
          Admitted.

      End JobWasErased.

      (* Since a job that is not erase retains its service,
         we can condense the lemmas about service at
		 later times into the following corollary. *)
      Corollary erase_service_after_erased_time:
        forall j,
          service new_sched j t_after =
          service sched j t_after - (sched t_erase == Some j).
      Proof.
        Admitted.
        
    End AfterEraseTime.

  End Lemmas.

End Erase.