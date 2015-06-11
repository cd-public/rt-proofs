Require Import Vbase List job schedule priority platform.

(* Mapping from processors to tasks at time t *)
Definition processor_list := schedule -> time -> list (option job).

(* Whether a schedule is produced by an identical multiprocessor *)
Definition ident_mp (num_cpus: nat) (hp: higher_priority) (cpumap: processor_list) (sched: schedule) :=

  (* An identical multiprocessor has a fixed number of cpus *)
  << mp_cpus_nonzero: num_cpus > 0 >> /\
  << mp_num_cpus: forall t, length (cpumap sched t) = num_cpus >> /\

  (* Job is scheduled iff it is mapped to a processor*)
  << mp_mapping: forall j t, List.In (Some j) (cpumap sched t) <-> scheduled sched j t >> /\

  (* A job receives at most 1 unit of service *)
  << mp_max_service: forall j t, service_at sched j t <= 1 >> /\

  (* Global scheduling invariant *)
  << mp_invariant:
       forall jlow t,
         backlogged sched jlow t <->
           (forall cpu, cpu < num_cpus ->
             (exists (jhigh: job), hp sched t jhigh jlow
                             /\ (nth cpu (cpumap sched t) None = Some jhigh))) >>.