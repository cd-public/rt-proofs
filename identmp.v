Add LoadPath "/home/felipec/dev/coq/rt-scheduling-spec".
Require Import Coq.Lists.List.
Require Import job.
Require Import schedule.

Axiom cpumap : schedule -> time -> list (option job).

Record ident_mp (num_cpus: nat) (sched: schedule) (hp: higher_priority) : Prop :=
  { ident_mp_cpus_nonzero: num_cpus > 0;

    (* Job is scheduled iff it is mapped to a processor*)
    ident_mp_mapping: forall (t: time),
                          (length (cpumap sched t) = num_cpus /\
                          (forall (j: job),
                              List.In (Some j) (cpumap sched t) <-> sched j t = 1));
    ident_mp_sched_unit: forall (j: job) (t: time), sched j t <= 1;

    (* Global scheduling invariant *)
    ident_mp_invariant:
        forall (jlow: job) (t: time),
            backlogged jlow sched t <->
                (forall (cpu: nat),
                cpu < num_cpus ->
                    (exists (jhigh: job),
                        (nth cpu (cpumap sched t) (Some jhigh) = Some jhigh)))
  }.