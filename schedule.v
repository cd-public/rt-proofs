Add LoadPath "/home/felipec/dev/coq/rt-scheduling-spec".
Require Import job.
Require Import Coq.Lists.ListSet.
Require Import Coq.Lists.List.

Definition time := nat.

Axiom schedule : Set.
(*Axiom scheduled : task -> schedule -> nat -> Prop.*)
Axiom exec : task -> schedule -> nat -> nat.

Definition cpu_platform := Set.
Axiom platform_of : schedule -> cpu_platform.

Record ident_mp (platform: cpu_platform) (num_cpus: nat) : Prop :=
  { ident_mp_maximum_exec: forall (tsk: task) (s: schedule) (t: time),
           platform_of s = platform -> exec tsk s t <= 1;
    ident_mp_mapping: forall (s: schedule) (t: time),
           platform_of s = platform ->
               (exists !(l: list task),
                   length l < num_cpus /\
                   forall (tsk: task),
                       List.In tsk l <-> exec tsk s t = 1)
  }.

Record unif_mp (platform: cpu_platform) (total_speed: nat) (max_speed: nat) : Prop :=
  { unif_mp_maximum_speed: forall (tsk: task) (s: schedule) (t: time),
          platform_of s = platform -> exec tsk s t <= max_speed;
    unif_mp_cumulative_speed:
          let exec2 (s: schedule) (t: time) (tsk:task) : nat := exec tsk s t in
              forall (s: schedule) (t: time),
                  platform_of s = platform ->
                      (exists ! (l: list task),
                          (forall (tsk: task), List.In tsk l <-> exec tsk s t > 0)
                          /\ (fold_left plus (map (exec2 s t) l) 0) <= total_speed)
  }.

Axiom cpu_list : cpu_platform -> list nat.
Axiom affinity : task -> cpu_platform -> list nat.

Record apa_ident_mp (platform: cpu_platform) (num_cpus: nat) : Prop :=
  { apa_ident_is_ident: ident_mp platform num_cpus;
    restricted_affinities:
        forall (s: schedule) (t: time),
            platform_of s = platform ->
            (forall (l: list task) (tsk: task) (cpu: nat),
                exec tsk s t = 1 ->
                cpu < num_cpus ->
                (nth cpu l tsk = tsk) ->
                List.In cpu (affinity tsk platform))
  }.

Fixpoint service (tsk: task) (s: schedule) (t: time) : nat:=
  match t with
  | 0 => exec tsk s 0
  | S n => service tsk s n + exec tsk s (S n)
  end.

Lemma exists_global_apa_platform :
    forall (platform: cpu_platform) (num_cpus: nat) (s: schedule),
        ident_mp platform num_cpus ->
        platform_of s = platform ->
        exists (platform': cpu_platform) (s': schedule),
            apa_ident_mp platform' num_cpus
            /\ platform_of s' = platform'.
            (*/\ (forall t: time, service tsk s t = service tsk s' t).*)