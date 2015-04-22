Add LoadPath "/home/felipec/dev/coq/rt-scheduling-spec".
Require Import Coq.Lists.List.
Require Import job.
Require Import schedule.
Require Import priority.

(* Mapping from processors to tasks at time t *)
Axiom cpumap : schedule -> time -> list (option job).

(* Whether a schedule is produced by an identical multiprocessor *)
Record ident_mp (num_cpus: nat) (sched: schedule) (hp: higher_priority) : Prop :=
  { (* An identical multiprocessor has a fixed number of cpus *)
    ident_mp_cpus_nonzero: num_cpus > 0;
    ident_mp_num_cpus: forall (t: time), length (cpumap sched t) = num_cpus;

    (* Job is scheduled iff it is mapped to a processor*)
    ident_mp_mapping: forall (j: job) (t: time),
                          List.In (Some j) (cpumap sched t) <-> sched j t = 1;

    (* A scheduled job only receives 1 unit of service *)
    ident_mp_sched_unit: forall (j: job) (t: time), sched j t <= 1;

    (* Global scheduling invariant *)
    ident_mp_invariant:
        forall (jlow: job) (t: time),
            backlogged jlow sched t <->
                (forall (cpu: nat),
                cpu < num_cpus ->
                    (exists (jhigh: job),
                        hp jhigh jlow sched t
                        /\ (nth cpu (cpumap sched t) None = Some jhigh)))
  }.