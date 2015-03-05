Require Import Coq.Lists.List.
Require Import Coq.Arith.EqNat.

Require Import job.

Definition processor := nat.
Definition time := nat.

Definition valid_taskset (ts: taskset) : Prop := List.Forall well_defined_task ts.

Record schedule_state : Type :=
  {
    instant: nat;
    cpu_count: nat;
    task_map: list (option job);
    active_jobs : list job
  }.

Definition scheduled (j: job) (cpu: processor) (s: schedule_state) : Prop :=
  nth cpu (task_map s) None = Some j.

Record valid_schedule_state (s: schedule_state) : Prop :=
  {
  number_cpus:
    length (task_map s) = cpu_count s;

  mutual_exclusion:
    forall j cpu1 cpu2, scheduled j cpu1 s ->
                        scheduled j cpu2 s ->
                        cpu1 = cpu2;
  task_map_is_valid:
    forall j cpu, scheduled j cpu s -> List.In j (active_jobs s)
  }.

Definition sched_algorithm := schedule_state -> Prop.

Fixpoint list_none (n:nat) : list (option job) :=
  match n with
  | O => nil
  | S n => None :: (list_none n)
  end.

Definition empty_schedule (num_cpus: nat) (state: schedule_state) : Prop :=
    instant state = 0 /\
    cpu_count state = num_cpus /\
    task_map state = list_none num_cpus /\
    active_jobs state = nil.

Definition arrives_at (t: time) (task: sporadic_task) : Prop :=
  exists job_num, st_arrival task job_num = t.

Definition job_index_at (job_num: nat) (t: time) (task: sporadic_task) : Prop :=
  exists t, st_arrival task job_num = t.

Definition create_job_at (t: time) (task: sporadic_task) : job :=
  {| job_id := task; (* TODO fix *)
     job_number := 0; (*TODO fix job_at t task;*)
     job_arrival := t;
     job_cost := st_cost task;
     job_deadline := st_deadline task
  |}.

Section Schedule.

Variable num_cpus: nat.
Variable alg: sched_algorithm.
Variable ts: taskset.

(*Definition preserves_validity (alg: sched_algorithm) : Prop :=
  exists state, valid_schedule_state state /\ alg state.*)

Definition add_arriving_tasks (t: time) (state: schedule_state) : Prop :=
  forall (task: sporadic_task),
    List.In task ts -> arrives_at t task -> List.In (create_job_at t task) (active_jobs state).

Parameter exec_time : job -> schedule_state -> nat. (*TODO fix*)
Definition completed (j: job) (state: schedule_state) : Prop :=
  exec_time j state = st_cost (job_id j).
Definition pending (j: job) (state: schedule_state) : Prop :=
  exec_time j state < st_cost (job_id j).

Definition keep_pending_tasks (state: schedule_state) (state': schedule_state) : Prop :=
  forall (j: job),
    List.In j (active_jobs state) -> pending j state' -> List.In j (active_jobs state').

Definition remove_completed_tasks (state: schedule_state) (state': schedule_state) : Prop :=
  forall (j: job),
    List.In j (active_jobs state) -> completed j state' -> ~List.In j (active_jobs state').

Definition initialize_execution (state: schedule_state) : Prop :=
  forall (j: job), List.In j (active_jobs state) -> exec_time j state = 0.

Definition advance_execution (state: schedule_state) (state': schedule_state) : Prop :=
  forall (j: job),
    List.In j (active_jobs state) ->
    exists cpu, scheduled j cpu state ->
    pending j state ->
    exec_time j state' = 1 + exec_time j state.

(*Definition sched_init (state: schedule_state) : Prop :=
  valid_taskset ts /\
  empty_schedule num_cpus state /\
  add_arriving_tasks 0 state /\
  initialize_execution state /\
  alg state.

Definition sched_next (state: schedule_state) (state': schedule_state) : Prop :=
  (*preserves_validity alg /\*)
  schedule state /\
  instant state' = S (instant state) /\
  add_arriving_tasks (S (instant state)) state' /\
  advance_execution state state' /\
  keep_pending_tasks state state' /\
  remove_completed_tasks state state' /\
  alg state'.*)

Inductive schedule : schedule_state -> Prop :=
  (* sched_init(num_cpus, alg, ts, state) determines an initial state *)
  | sched_init : forall (state: schedule_state),
        valid_taskset ts ->
        empty_schedule num_cpus state ->
        add_arriving_tasks 0 state ->
        initialize_execution state ->
        alg state ->
        schedule state
  (* sched_next(num_cpus, alg, ts, state, state') relates two consecutive states *)
  | sched_next : forall (state: schedule_state) (state': schedule_state),
        (*preserves_validity alg ->*)
        schedule state ->
        instant state' = S (instant state) ->
        add_arriving_tasks (S (instant state)) state' ->
        advance_execution state state' ->
        keep_pending_tasks state state' ->
        remove_completed_tasks state state' ->
        alg state' ->
        schedule state'.

Lemma length_list_none : forall (n: nat), length (list_none n) = n.
Proof.
  intros n. induction n as [| n'].
    trivial.
    simpl. rewrite IHn'. trivial.
  Qed.

Lemma nth_list_none: forall n cpu,
  nth cpu (list_none n) None = None.
Proof.
  induction n; intros; simpl; destruct cpu; auto.
Qed.

Lemma empty_schedule_valid : forall (state: schedule_state) (num_cpus: nat),
                                 empty_schedule num_cpus state -> valid_schedule_state state.
Proof.
  intros. inversion H as [H0 [H1 [H2 H3]]].
  constructor. rewrite H1. rewrite H2. apply length_list_none.
  unfold scheduled. intros j cpu1 cpu2. rewrite H2. rewrite 2 nth_list_none. intros. inversion H4.
  intros. inversion H4. rewrite H2 in H6. rewrite nth_list_none in H6. inversion H6.
Qed.

Theorem schedule_always_valid :
  forall (t: time) (state: schedule_state) (sched: schedule state),
    valid_schedule_state state.
Proof.
  intros. induction sched. apply empty_schedule_valid in H0. apply H0.
  admit. (* TODO fix *)
Qed.

Definition cpu_idle (cpu: processor) (s: schedule_state) : Prop :=
  forall j, ~scheduled j cpu s.

Definition job_backlogged (j: job) (s: schedule_state) : Prop :=
  List.In j (active_jobs s) /\ forall cpu, ~scheduled j cpu s.

Definition break_ties (j1 j2: job) : Prop :=
  st_id (job_id j1) < st_id (job_id j2) \/ job_number j1 < job_number j2.

Definition prio_order := job -> job -> Prop. (* job_a < job_b *)

Definition prio_EDF (j1 j2: job) : Prop :=
  job_deadline j1 < job_deadline j2 \/ break_ties j1 j2.

Definition enforce_priority (higher_prio: prio_order) (s: schedule_state) : Prop := forall cpu,
  cpu_idle cpu s
  \/ (exists j, scheduled j cpu s -> (forall b, job_backlogged b s -> higher_prio j b)). 

(* TODO add unique priorities *)
(* TODO add some predicates to indicate CPU allowance -> add affinities in the future *)

Definition work_conserving (s: schedule_state) : Prop :=
  forall cpu, cpu_idle cpu s -> forall j, ~job_backlogged j s.

Definition sched_EDF (s: schedule_state) : Prop :=
  work_conserving s /\ enforce_priority prio_EDF s.
Check sched_next.

Require Import Coq.Relations.Relations.

Theorem bla : sched_next = relation.

Definition apply_next (n: nat) (state: schedule_state) (sched: schedule t state) : time -> schedule_state -> Prop :=
  match sched with
  | sched_init state' _ _ _ _ _ => sched_next state _ _ _ _ _ _ state'
  end.

Definition reaches (s: schedule) (state: schedule_state) (state': schedule_state) : Prop :=
  

Definition response_time (j: job) (s: schedule) : nat :=
  (forall (state: schedule_state) (state': schedule_state), completed j s /\ completed j s' -> reaches s s'.

Definition response_time_bound (task: sporadic_task) : Prop :=