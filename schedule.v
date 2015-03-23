Add LoadPath "/home/felipec/dev/coq/rt-scheduling-spec".
Require Import job.
Require Import Coq.Lists.ListSet.
Require Import Coq.Lists.List.
Require Import helper.

Definition time := nat.

Definition schedule := task -> time -> Prop.
Axiom exec : schedule -> task -> time -> nat.

Axiom no_sched_no_exec : forall (s: schedule) (tsk: task) (t: time),
                             exec s tsk t > 0 <-> s tsk t.

Record ident_mp (num_cpus: nat) (s: schedule) : Prop :=
  { ident_mp_cpus_nonzero: num_cpus > 0;
    ident_mp_exec: forall (tsk: task) (t: time), s tsk t <-> exec s tsk t = 1;
    ident_mp_mapping: forall (t: time),
                          (exists !(l: list (option task)),
                              length l = num_cpus /\
                              (forall (tsk: task),
                                  List.In (Some tsk) l <-> s tsk t))
  }.

Definition affinity := task -> schedule -> list nat.

Record apa_ident_mp (num_cpus: nat) (s: schedule) (alpha: affinity) : Prop :=
  { apa_ident_is_ident: ident_mp num_cpus s;
    restricted_affinities:
        forall (t: time),
            (forall (l: list (option task)) (tsk: task) (cpu: nat),
                s tsk t ->
                cpu < num_cpus ->
                (nth cpu l (Some tsk) = Some tsk) ->
                List.In cpu (alpha tsk s))
  }.

Fixpoint service (s: schedule) (tsk: task) (t: time) : nat:=
  match t with
  | 0 => exec s tsk 0
  | S t => service s tsk t + exec s tsk (S t)
  end.

Lemma exists_global_apa_platform :
    forall (num_cpus: nat) (s: schedule),
        ident_mp num_cpus s ->
        exists (s': schedule) (alpha: affinity),
            apa_ident_mp num_cpus s alpha
            /\ (forall (tsk: task) (t: time), service s tsk t = service s' tsk t).
Proof. intros. exists s. exists (fun (tsk : task) (s: schedule) => (seq 0 num_cpus)).
       split. split. apply H.
       intros. apply nat_seq_nth_In. apply H1.
       trivial.
Qed.