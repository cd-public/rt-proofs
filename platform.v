Require Import Vbase ScheduleDefs PriorityDefs.

Module Platform.

Import Schedule.

(* A processor platform is simply a set of schedules, \ie.,
   it defines the amount of service that jobs receive over time. *)

Definition processor_platform := schedule -> Prop.

(* For a processor platform to be valid, it must be able to schedule
   any possible job arrival sequence. In particular, the constraints
   of the platform should not be trivially false. *)
Definition valid_platform (plat: processor_platform) :=
  forall (arr: arrival_sequence),
    exists (sched: schedule), (arr_seq_of_schedule sched = arr) /\ plat sched.

End Platform.

Module IdenticalMultiprocessor.

Import Schedule Platform Priority.

Section Multiprocessor.
  
Variable higher_priority: jldp_policy.
Variable num_cpus: nat.
Variable sched: schedule.

  (* The mapping has a finite positive number of cpus: [0, num_cpus) *)
Definition mp_cpus_nonzero: num_cpus > 0.
Definition mp_num_cpus: forall j cpu t, mapped j cpu t -> cpu < num_cpus.  >> /\

  (* Job is scheduled iff it is mapped to some processor*)
  << mp_mapping: forall j t, scheduled sched j t <-> exists cpu, mapped j cpu t >> /\

  (* Non-parallelism restrictions (mapping must be an injective function) *)
  << mp_mapping_fun: forall j cpu cpu' t, mapped j cpu t /\ mapped j cpu' t -> cpu = cpu' >> /\
  << mp_mapping_inj: forall j j' cpu t, mapped j cpu t /\ mapped j' cpu t -> j = j'>> /\
  
  (* A job receives at most 1 unit of service *)
  << mp_max_service: forall j t, service_at sched j t <= 1 >> /\

  (* Global scheduling invariant *)
  << mp_invariant: forall jlow t (ARRIVED: arrived sched jlow t),
    backlogged sched jlow t <->
      (exists (j0: job), earlier_job sched j0 jlow /\ pending sched j0 t) \/
      (forall cpu (MAXcpu: cpu < num_cpus),
       exists jhigh, hp sched t jhigh jlow /\ mapped jhigh cpu t) >>.

(* TODO/Observations *)
(* 1) Note that the scheduling invariant only applies to jobs that
      have arrived in the schedule, thus the need for (ARRIVED: ...).
      If all processors are occupied by higher-priority
      jobs, it doesn't mean that a random job jlow (not part of the
      task set) is backlogged.
 *)

Definition my_service_at (my_j j: job) (t: time) :=
  if my_j == j then
    (if t < task_cost (job_task j) then 1 else 0)
  else 0.

Definition my_arr_seq (my_j: job) (t: nat) :=
  if (t == 0) then [::my_j] else [::].
