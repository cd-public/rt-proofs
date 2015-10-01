Require Import Vbase ScheduleDefs JobDefs PriorityDefs TaskArrivalDefs
               ssreflect ssrbool eqtype ssrnat seq.

(*Module Platform.

Import Schedule.

(* A processor platform is simply a set of schedules, \ie.,
   it specifies the amount of service that jobs receive over time. *)
Definition processor_platform := schedule_mapping -> Prop.

(* For a processor platform to be valid, it must be able to schedule
   any possible job arrival sequence. In particular, the constraints
   of the platform should not be trivially false. *)
(*Definition valid_platform (plat: processor_platform) :=
  exists (sched: schedule), plat sched.*)

(* Whether a job receives at most 1 unit of service *)
Definition max_service_one (sched: schedule) := forall j t, service_at sched j t <= 1.

End Platform.

Module IdenticalMultiprocessor.

Import Job ScheduleOfSporadicTask Platform Priority SporadicTaskArrival.

Section Multiprocessor.

Variable num_cpus: nat.
Variable higher_eq_priority: jldp_policy.
Variable sched: schedule.

(* There is at least one processor. *)
Definition mp_cpus_nonzero := num_cpus > 0.

(* At any time,
     (a) processors never stay idle when there are pending jobs (work conservation), and,
     (b) the number of scheduled jobs does not exceed the number of processors. *)
Definition mp_work_conserving :=
  forall t, num_scheduled_jobs sched t = minn (num_pending_jobs sched t) num_cpus.

(* If a job is backlogged, then either:
     (a) there exists an earlier pending job of the same task
     (b) all processor are busy with (other) jobs with higher or equal priority. *)
Definition mp_scheduling_invariant :=
  forall jlow t (ARRIVED: jlow \in prev_arrivals sched t)
         (BACK: backlogged sched jlow t),
    exists_earlier_job sched t jlow \/
    num_interfering_jobs higher_eq_priority sched t jlow = num_cpus.

Definition identical_multiprocessor :=
  mp_cpus_nonzero /\ mp_scheduling_invariant /\ mp_work_conserving.

End Multiprocessor.

Section Uniprocessor.

(* Uniprocessor is a special case of a multiprocessor *)
Definition uniprocessor := identical_multiprocessor 1.

End Uniprocessor.

(*Lemma identmp_valid :
  forall num_cpus higher_eq_priority,
    valid_platform (identical_multiprocessor num_cpus higher_eq_priority).
Proof.
  unfold valid_platform, identical_multiprocessor, mp_cpus_nonzero,
  mp_scheduling_invariant; ins.
Qed.*)

End IdenticalMultiprocessor. *)