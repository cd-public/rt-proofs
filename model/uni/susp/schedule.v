Require Import rt.util.all.
Require Import rt.model.arrival_sequence rt.model.suspension
               rt.model.priority.
Require Import rt.model.uni.schedule.
Require Import rt.model.uni.susp.suspension_intervals.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Module ScheduleWithSuspensions.

  Export UniprocessorSchedule SuspensionIntervals.

  Section Definitions.
    
    Context {Task: eqType}.
    Context {Job: eqType}.
    Variable job_cost: Job -> time.

    (* Assume that job suspension times are given. *)
    Variable next_suspension: job_suspension Job.

    (* Consider any uniprocessor schedule. *)
    Context {arr_seq: arrival_sequence Job}.
    Variable sched: schedule arr_seq.

    (* Recall the predicates that denote whether a job is scheduled
       and suspended. *)
    Let job_pending_at := pending job_cost sched.
    Let job_scheduled_at := scheduled_at sched.
    Let job_suspended_at := suspended_at job_cost next_suspension sched.

    (* First, we redefine the notion of backlogged job to account for suspensions. *)
    Section BackloggedJob.

      (* We say that job j...*)
      Variable j: JobIn arr_seq.

      (* ...is backlogged at time t iff it is pending and neither
         scheduled nor suspended. *)
      Definition backlogged (t: time) :=
        job_pending_at j t
        && ~~ job_scheduled_at j t
        && ~~ job_suspended_at j t.

    End BackloggedJob.

  End Definitions.
  
End ScheduleWithSuspensions.