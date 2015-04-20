Add LoadPath "/home/felipec/dev/coq/rt-scheduling-spec".
Require Import Coq.Lists.List.
Require Import job.
Require Import schedule.
Require Import helper.

Definition affinity := job -> schedule -> list nat.

Record apa_ident_mp (num_cpus: nat) (sched: schedule) (alpha: affinity) : Prop :=
  { apa_ident_is_ident: ident_mp num_cpus sched;
    restricted_affinities:
        forall (t: time),
            (forall (l: list (option job)) (j: job) (cpu: nat),
                sched j t = 1 ->
                cpu < num_cpus ->
                (nth cpu l (Some j) = Some j) ->
                List.In cpu (alpha j sched))
  }.

Lemma exists_apa_platform_that_is_global :
    forall (num_cpus: nat) (s: schedule),
        ident_mp num_cpus s ->
        exists (s': schedule) (alpha: affinity),
            apa_ident_mp num_cpus s alpha
            /\ (forall (j: job) (t: time), service s j t = service s' j t).
Proof. intros. exists s. exists (fun (j : job) (s: schedule) => (seq 0 num_cpus)).
       split. split. apply H.
       intros. apply nat_seq_nth_In. apply H1.
       trivial.
Qed.