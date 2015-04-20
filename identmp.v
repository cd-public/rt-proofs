Add LoadPath "/home/felipec/dev/coq/rt-scheduling-spec".
Require Import Coq.Lists.List.
Require Import job.
Require Import schedule.

Record ident_mp (num_cpus: nat) (sched: schedule) : Prop :=
  { ident_mp_cpus_nonzero: num_cpus > 0;
    ident_mp_mapping: forall (t: time),
                          (exists !(l: list (option job)),
                              length l = num_cpus /\
                              (forall (j: job),
                                  List.In (Some j) l <-> sched j t = 1));
    ident_mp_sched_unit: forall (j: job) (t: time), sched j t <= 1
  }.