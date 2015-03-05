Require Import Coq.Lists.List.
Require Import Coq.Arith.EqNat.

Require Import job.

Definition processor := nat.
Definition time := nat.

Definition valid_taskset (ts: taskset) : Prop := List.Forall well_defined_task ts.

Record schedule_state : Type :=
  {
    instant: time;
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

Definition empty_schedule (num_cpus: nat) : schedule_state :=
  {|
    instant := 0;
    cpu_count := num_cpus;
    task_map := list_none num_cpus;
    active_jobs := nil
  |}.

Definition add_job (j: job) (s: schedule_state) : schedule_state :=
  {|
    instant := instant s;
    cpu_count := cpu_count s;
    task_map := task_map s;
    active_jobs := cons j (active_jobs s) 
  |}.

Fixpoint has_job_arrival_at (t: time) (task: sporadic_task) : bool := true. (*TODO: fix*)
Fixpoint job_at (t:time) (task: sporadic_task) : nat := 0. (*TODO: fix*)

Definition create_job_at (t: time) (task: sporadic_task) : job :=
  {| job_id := st_id task;
     job_number := job_at t task;
     job_arrival := t;
     job_cost := st_cost task;
     job_deadline := st_deadline task
  |}.

Definition arriving_jobs (ts: taskset) (t: time) : list job :=
    List.map (create_job_at t) (List.filter (has_job_arrival_at t) ts).

Definition process_arrivals (ts: taskset) (s: schedule_state) : schedule_state :=
  fold_right add_job s (arriving_jobs ts (instant s)).

Definition process_completions (s: schedule_state) : schedule_state := s. (*TODO: fix*)

Definition advance_schedule (ts: taskset) (s: schedule_state) : schedule_state :=
  process_completions
    (process_arrivals ts
      {| instant := (instant s)+1; 
         cpu_count := cpu_count s;
         task_map := task_map s;
         active_jobs := active_jobs s |}).

Definition preserves {X: Type} (P: X -> Prop) (f: X -> X) : Prop :=
  forall (x: X), P x -> P (f x).

Definition preserves_validity := preserves valid_schedule_state.

Inductive schedule (num_cpus: nat) (alg: sched_algorithm) (ts: taskset):
               schedule_state -> Type :=
  (* sched_init(alg, ts) gives the initial state *)
  | sched_init : forall (state: schedule_state),
        valid_taskset ts ->
        preserves_validity alg ->
        schedule num_cpus alg ts
          (alg (process_arrivals ts (empty_schedule num_cpus)))
  (* sched_next(alg, ts, state) moves to the next state *)
  | sched_next : forall (state: schedule_state),
        preserves_validity alg ->
        schedule num_cpus alg ts state ->
        schedule num_cpus alg ts (advance_schedule ts state).

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

Fixpoint exec_time (num_cpus: nat) (alg: sched_algorithm) (ts: taskset) (state: schedule_state)
                                 (sched: schedule num_cpus alg ts state) (j: job) : nat :=
  if ble_nat (job_arrival j) (instant state) then
      match sched with
      | sched_init prev_state _ _  => 0
      | sched_next prev_state _ prev_sched =>
        if true then (*TODO fix *)
            1 + exec_time num_cpus alg ts prev_state prev_sched j
        else
            exec_time num_cpus alg ts prev_state prev_sched j
      end 
  else 0.

Definition completed (num_cpus: nat) (alg: sched_algorithm) (ts: taskset) (state: schedule_state)
                                 (sched: schedule num_cpus alg ts state) (j: job) : bool :=
  beq_nat (exec_time num_cpus alg ts state sched j) (job_cost j).

Definition pending (num_cpus: nat) (alg: sched_algorithm) (ts: taskset) (state: schedule_state)
                                 (sched: schedule num_cpus alg ts state) (j: job) : bool :=
  negb (completed num_cpus alg ts state sched j).

(*Definition completed {num_cpus: nat} {alg: sched_algorithm} {ts: taskset} {state: schedule_state}
                                 (sched: schedule num_cpus alg ts state) (j: job) : Prop :=
  exec_time num_cpus alg ts state sched j = job_cost j.*)

Definition clear_completed (num_cpus: nat) (alg: sched_algorithm) (ts: taskset) (state: schedule_state)
                                 (sched: schedule num_cpus alg ts state) (j: job) : option job :=
  match (completed num_cpus alg ts state sched j) with
  | true => None
  | false => Some j
  end.

Definition process_completions (s: schedule_state) : schedule_state :=
  {| instant := instant s; 
     cpu_count := cpu_count s;
     task_map := map (clear_completed num_cpus alg ts state sched) (task_map s);
     active_jobs := forallb (pending num_cpus alg ts state sched) (active_jobs s)
  |}.

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

Lemma empty_schedule_valid : forall (num_cpus: nat),
                                 valid_schedule_state (empty_schedule num_cpus).
Proof.
  intros; constructor; simpl;  eauto using length_list_none;
  intros; inversion H as [X]; rewrite nth_list_none in X; inversion X.
Qed.

Lemma fold_preserves : forall (s: schedule_state) (l: list job) (P: schedule_state-> Prop),
  P (s) -> (forall (j: job), preserves P (add_job j)) -> P (fold_right add_job s l).
Proof.
  unfold preserves. intros.
  induction l.
    simpl. apply H.
    simpl. apply H0. apply IHl.
Qed.

Lemma process_arrivals_maintains_state : forall (s: schedule_state) (ts: taskset),
    instant s = instant (process_arrivals ts s) /\
    cpu_count s = cpu_count (process_arrivals ts s) /\
    task_map s = task_map (process_arrivals ts s).
Proof.
  intros. assert (H0:=fold_preserves). split.
  unfold process_arrivals. apply H0. reflexivity.
  unfold preserves. intros. apply H. split.
  unfold process_arrivals. apply H0. reflexivity.
  unfold preserves. intros. apply H.
  unfold process_arrivals. apply H0. reflexivity.
  unfold preserves. intros. apply H.
Qed.

Lemma process_arrivals_valid : forall (ts: taskset),  preserves_validity (process_arrivals ts).
Proof.
  intro ts. unfold preserves_validity. unfold preserves. intro x.
  assert (H0 := process_arrivals_maintains_state x ts). inversion H0 as [H1 [H2 H3]].
  constructor. inversion H.
  rewrite <- H2. rewrite <- H3. apply number_cpus0.
  unfold scheduled. rewrite <- H3. intros. inversion H. apply mutual_exclusion0 with (j:=j).
  apply H4. apply H5.
  unfold scheduled. intros. inversion H. rewrite <- H3 in H4.
  apply task_map_is_valid0 in H4.
  unfold process_arrivals. apply fold_preserves.
  apply H4.
  unfold preserves. intros.
  induction x0. simpl. apply or_intror. apply H5. Qed.

Lemma process_completions_valid : forall (ts: taskset),  preserves_validity (process_arrivals ts).
Proof.
  intro ts. unfold preserves_validity. unfold preserves. intro x.
  assert (H0 := process_arrivals_maintains_state x ts). inversion H0 as [H1 [H2 H3]].
  constructor. inversion H.
  rewrite <- H2. rewrite <- H3. apply number_cpus0.
  unfold scheduled. rewrite <- H3. intros. inversion H. apply mutual_exclusion0 with (j:=j).
  apply H4. apply H5.
  unfold scheduled. intros. inversion H. rewrite <- H3 in H4.
  apply task_map_is_valid0 in H4.
  unfold process_arrivals. apply fold_preserves.
  apply H4.
  unfold preserves. intros.
  induction x0. simpl. apply or_intror. apply H5. Qed.

Lemma advance_schedule_valid : forall (ts: taskset), preserves_validity (advance_schedule ts).
Proof.
  admit.
Qed.

Theorem schedule_always_valid : forall (num_cpus: nat) (alg: sched_algorithm) (ts: taskset)
                                                                (state: schedule_state) (sched: schedule num_cpus alg ts state),
                                                                    valid_schedule_state state.
Proof.
  intros. induction sched.
  apply p. apply process_arrivals_valid. apply empty_schedule_valid.
  apply advance_schedule_valid. apply IHsched.
Qed.

Definition sched_edf (s: schedule_state) : schedule_state := s. (*TODO fix *)

Definition deadline_miss (j: job) (s: schedule) : Prop := True.
















match s with
  |  sched_init num_cpus ts state _ _ => True
  end.

(* arrives_at (schedule, task, job_num, time): All possible arrival sequences for a job *)
Inductive arrives_at (s: schedule) (task: sporadic_task) : nat -> time -> Prop :=
  | arrives_at_offset: arrives_at s task 0 (st_offset task)
  | arrives_next: forall (num_job: nat) (t: time) (k: nat),
                                   arrives_at s task num_job t ->
                                   arrives_at s task (num_job + 1) (t + (st_period task) + k).

Definition active_at (s: schedule) (task: sporadic_task) (num_job: nat) (t: time) : Prop :=
  forall (t0: time), arrives_at s task num_job t0 /\ t0 <= t.

Parameter scheduled_at: schedule -> sporadic_task -> nat -> time -> Prop.





Definition first_job (t: sporadic_task) : job :=
  {| job_id := st_id t;
     job_number := 0;
     job_arrival := st_offset t;
     job_cost := st_cost t;
     job_deadline := st_deadline t
  |}.