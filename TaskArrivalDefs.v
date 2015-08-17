Require Import Classical Vbase TaskDefs JobDefs ScheduleDefs helper
               ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Module SporadicTaskArrival.

Import SporadicTaskJob SporadicTaskset Schedule.
  
(* Whether the arrival sequence of a schedule is induced by a task set *)
Definition ts_arrival_sequence (ts: sporadic_taskset) (sched: schedule) :=
  forall j t (ARR: arrives_at sched j t), (job_task j) \in ts.


(*Definition interarrival_times (sched: schedule) :=
  forall j arr (ARR: arrives_at sched j arr)
         j' (NEQ: j <> j') arr' (LE: arr <= arr')
         (EQtsk: job_task j' = job_task j)
         (ARR': arrives_at sched j' arr'),
    arr' >= arr + task_period (job_task j).*)

Definition periodic_task_model (ts: sporadic_taskset) (sched: schedule) :=
  << ARRts: ts_arrival_sequence ts sched >> /\
  << NEXT:
    forall j arr (ARRj: arrives_at sched j arr) j' (NEQ: j <> j')
           arr' (LE: arr <= arr') (ARRj': arrives_at sched j' arr),
      arr' = arr + task_period (job_task j) >>.

Definition sporadic_task_model (ts: sporadic_taskset) (sched: schedule) :=
  << ARRts: ts_arrival_sequence ts sched >> /\
  << NEXT:
    forall j arr (ARRj: arrives_at sched j arr) j' (NEQ: j <> j')
           arr' (LE: arr <= arr') (ARRj': arrives_at sched j' arr),
      arr' >= arr + task_period (job_task j) >>.

(* Synchronous release at time t *)
Definition sync_release (ts: sporadic_taskset) (sched: schedule) (t: time) :=
  << ARRts: ts_arrival_sequence ts sched >> /\
  forall (tsk: sporadic_task) (IN: tsk \in ts),
    exists (j: job), job_task j = tsk /\ arrives_at sched j t.

Section UniqueArrivals.

Variable sched: schedule.
Variable t: time.

Hypothesis no_multiple_job_arrivals: no_multiple_arrivals (arr_seq_of sched).
Hypothesis arr_seq_uniq: arrival_sequence_unique (arr_seq_of sched).

Lemma uniq_prev_arrivals : uniq (prev_arrivals sched t).
Proof.
  unfold arrival_sequence_unique, no_multiple_arrivals in *;
  rename arr_seq_uniq into UNIQ, no_multiple_job_arrivals into NOMULT.
  induction t; first by unfold prev_arrivals; rewrite -/prev_arrivals big_geq //.
  unfold prev_arrivals; rewrite big_nat_recr // /=.
  rewrite cat_uniq; apply/and3P; split; [by ins | | by apply UNIQ].
  apply/hasP; unfold not; intro HAS; destruct HAS as [x IN MEM]; rewrite -unfold_in mem_mem in MEM.
  rewrite in_prev_arrivals_iff_arrived_before in MEM; move: MEM => /exists_inP_nat MEM; des.
  by apply (NOMULT x t0 x0) in MEM0; [by subst; rewrite ltnn in MEM | by ins].
Qed.

End UniqueArrivals.

End SporadicTaskArrival.