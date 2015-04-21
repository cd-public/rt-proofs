Add LoadPath "/home/felipec/dev/coq/rt-scheduling-spec".
Require Import Coq.Lists.List.
Require Import job.
Require Import schedule.
Require Import priority.
Require Import helper.
Require Import identmp.

Definition affinity := job -> list nat.

Record apa_ident_mp (num_cpus: nat) (sched: schedule) (alpha: affinity) (hp: higher_priority) : Prop :=
  { apa_ident_mp_cpus_nonzero: num_cpus > 0;

    (* Job is scheduled iff it is mapped to a processor*)
    apa_ident_mp_mapping: forall (t: time),
                          (length (cpumap sched t) = num_cpus /\
                          (forall (j: job),
                              List.In (Some j) (cpumap sched t) <-> sched j t = 1));
    apa_ident_mp_sched_unit: forall (j: job) (t: time), sched j t <= 1;

    (* If some job is scheduled, then its affinity should allow it. *)
    apa_ident_mp_restricted_affinities:
        forall (t: time) (j: job) (cpu: nat),
                sched j t = 1 ->
                cpu < num_cpus ->
                (nth cpu (cpumap sched t) (None) = Some j) ->
                List.In cpu (alpha j);

    (* (Weak) APA scheduling invariant *)
    apa_ident_mp_invariant:
        forall (jlow: job) (t: time),
            backlogged jlow sched t <->
                (forall (cpu: nat),
                cpu < num_cpus /\
                List.In cpu (alpha jlow) ->
                    (exists (jhigh: job),
                        hp jhigh jlow sched t
                        /\ (nth cpu (cpumap sched t) (None) = Some jhigh)))
  }.

Lemma exists_apa_platform_that_is_global :
    forall (num_cpus: nat) (s: schedule) (hp: higher_priority),
        ident_mp num_cpus s hp ->
        exists (s': schedule) (alpha: affinity),
            apa_ident_mp num_cpus s alpha hp
            /\ (forall (j: job) (t: time), service s j t = service s' j t).
Proof. intros. inversion H. exists s. exists (fun (j : job) => (seq 0 num_cpus)).
       split. split.
       apply ident_mp_cpus_nonzero.
       apply ident_mp_mapping.
       apply ident_mp_sched_unit.
       intros. apply nat_seq_nth_In. apply H1.
       intros. assert (H1 := ident_mp_invariant jlow t).
       inversion H1. split.
       intros. assert (H5 := H0 H3 cpu). inversion H4.
       apply H5 in H6. trivial.
       intros. apply H2. intros.
       assert (H5 := H3 cpu). assert (H6 := nat_seq_nth_In num_cpus cpu H4).
       assert (H7 := H5 (conj H4 H6)). trivial. trivial.
Qed.

Lemma APA_service_invariant :
    forall (num_cpus: nat) (sched: schedule) (j: job) (t: time) (hp: higher_priority)
           (alpha: affinity) (alpha': affinity),
               apa_ident_mp num_cpus sched alpha hp
               -> exists (sched': schedule),
                      (apa_ident_mp num_cpus sched' alpha' hp
                       /\ service sched j t >= service sched' j t).
Proof.
    Admitted.