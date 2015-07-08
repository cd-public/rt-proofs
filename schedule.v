Require Import List Classical Arith.Gt Vbase task job helper.

(* Integer time *)
Definition time := nat.

(* Set of all possible job arrival sequences *)
Record arrival_sequence : Type :=
{
  arr :> job -> time -> Prop;
  no_multiple_arrivals: forall j t1 t2, arr j t1 -> arr j t2 -> t1 = t2
}.

(* Observations/ TODO *)
(* 1) This definition of arrival sequence allows referring to any job that arrives
      at time t. But it doesn't allow retrieving the finite set of jobs that
      have arrived up to time t. We need to assume decidability somehow
      and return a list.
*)

Record schedule_data : Type :=
{
  (* service received by a job during [t, t+1) *)
  service_at: job -> time -> nat;
  (* arrival sequence of the schedule *)
  arrives_at: arrival_sequence
}.

(* Cumulative service received by a job in a schedule, during [0, t+1) *)
Fixpoint service (sched: schedule_data) (j: job) (t: time) : nat :=
  match t with
      | 0 => service_at sched j 0
      | S t => service sched j t + service_at sched j (S t)
  end.

(* Whether a job arrived at time t *)
Definition arrived (sched: schedule_data) (j: job)  (t: time) :=
  exists t_0, t_0 <= t /\ (arrives_at sched) j t_0.

(* Whether a job is scheduled at time t *)
Definition scheduled (sched: schedule_data) (j: job) (t: time) :=
  service_at sched j t <> 0.

(* Whether a job has completed at time t (assumes costs are non-zero!) *)
Definition completed (sched: schedule_data) (j: job) (t: time) :=
  t <> 0 /\ service sched j (t-1) = job_cost j.

Definition pending (sched: schedule_data) (j: job) (t: time) :=
  arrived sched j t /\ ~completed sched j t.

(* Whether a job is pending and not scheduled at time t *)
Definition backlogged (sched: schedule_data) (j: job) (t: time) :=
  pending sched j t /\ ~scheduled sched j t.

Record schedule : Type :=
{
  sd:> schedule_data;

  sched_properties:
    (* A job can only be scheduled if it arrived *)
    << task_must_arrive_to_exec: forall j t, scheduled sd j t -> arrived sd j t >> /\

    (* A job cannot be scheduled after it completed *)
    << comp_task_no_exec:
       forall j t t_comp (jComp: completed sd j t_comp) (tAfter: t >= t_comp), ~ scheduled sd j t >>
}.

Definition earlier_job (sched: schedule) (j1 j2: job) :=
  << EQtsk: job_task j1 = job_task j2 >> /\
  exists arr1 arr2, << ARR1: arrives_at sched j1 arr1 >> /\
                    << ARR2: arrives_at sched j2 arr2 >> /\
                    << LT: arr1 < arr2 >>.
  
Lemma backlogged_no_service : forall sched j t,
  backlogged sched j t -> service_at sched j t = 0.
Proof.
  unfold backlogged, scheduled; ins; des.
  destruct (service_at sched j t); eauto; intuition.
Qed.

Lemma no_completed_tasks_at_time_zero : forall sched j, completed sched j 0 -> False.
Proof.
  unfold completed; ins; des; eauto.
Qed.

Lemma not_arrived_no_service :
  forall (sched: schedule) j t_a (jArr: arrives_at sched j t_a) t_0 (t0Before: t_0 < t_a), service sched j t_0 = 0.
Proof.
  ins; des.
  assert (schedProp := sched_properties sched); des; clear comp_task_no_exec.
  induction t_0; simpl.
    (* Base case *)
    destruct (classic (scheduled sched j 0)) as [SCHED | notSCHED]; unfold scheduled in *; [| by intuition].
    {
      apply task_must_arrive_to_exec in SCHED.
      unfold arrived in SCHED; des.
      assert (t_0 = t_a); eauto using no_multiple_arrivals; subst.
      intuition.
    }
    
    (* Inductive step *)
    rewrite IHt_0; [simpl | by omega].
    destruct (classic (scheduled sched j (S t_0))) as [SCHED | notSCHED]; unfold scheduled in *; [| by intuition].
    {
      apply task_must_arrive_to_exec in SCHED.
      unfold arrived in SCHED; des.
      assert (t_1 = t_a); eauto using no_multiple_arrivals; subst.
      intuition.
    }
Qed.