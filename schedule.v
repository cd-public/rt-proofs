Add LoadPath "/home/felipec/dev/coq/rt-scheduling-spec".
Require Import job.
Require Import Coq.Lists.ListSet.
Require Import Coq.Lists.List.
Require Import helper.

Definition time := nat.

Definition arrival_seq := job -> time -> Prop.

Record ts_arrival_seq (ts: taskset) (arr: arrival_seq) : Prop :=
  { job_of_task_arrives: forall (j: job) (tsk: sporadic_task) (t: time),
        arr j t /\ job_of j tsk <-> List.In tsk ts;
    inter_arrival_times:
        forall (j1: job) (j2: job) (tsk: sporadic_task) (t: time) (t': time),
            (arr j1 t /\ arr j2 t' /\ t < t'
            /\ job_of j1 tsk /\ job_of j2 tsk)
            -> t < t' + task_period tsk 
  }.

Definition schedule := job -> time -> nat.

Record ident_mp (num_cpus: nat) (sched: schedule) : Prop :=
  { ident_mp_cpus_nonzero: num_cpus > 0;
    ident_mp_mapping: forall (t: time),
                          (exists !(l: list (option job)),
                              length l = num_cpus /\
                              (forall (j: job),
                                  List.In (Some j) l <-> sched j t = 1));
    ident_mp_sched_unit: forall (j: job) (t: time), sched j t <= 1
  }.

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

Fixpoint service (sched: schedule) (j: job) (t: time) : nat:=
  match t with
  | 0 => sched j 0
  | S t => service sched j t + sched j (S t)
  end.

Axiom task_completed :
    forall (j: job) (sched: schedule) (t_comp: time),
        service sched j t_comp = job_cost j ->
            forall (t: time), t >= t_comp -> sched j t = 0.        

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