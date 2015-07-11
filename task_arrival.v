Require Import List Classical Vbase task job schedule.

(* Whether the arrival sequence of a schedule is induced by a task set *)
Definition ts_arrival_sequence (ts: taskset) (sched: schedule) :=
  forall j t (ARR: arrives_at sched j t), In (job_task j) ts.

Definition task_job_unique (sched: schedule) :=
  forall t j1 j2 (EQtsk: job_task j1 = job_task j2)
         (ARR1: arrives_at sched j1 t) (ARR2: arrives_at sched j2 t),
    j1 = j2.

(* Since the number of tasks is finite, and each task does not
   spawn more than one job per time instant, the number of jobs
   released in a bounded interval is finite. *)
Definition arrival_list (sched: schedule) (l: list job) (t: time) :=
  forall j, In j l <-> arrived sched j t.

Lemma released_jobs_at:
  forall ts sched (ARRts: ts_arrival_sequence ts sched)
         (UNIQUE: task_job_unique sched) t,
    exists (l: list job),
      forall j, In j l <-> arrives_at sched j t.
Proof.
  unfold task_job_unique, ts_arrival_sequence; ins.
  cut (exists l, forall j, In j l <-> arrives_at sched j t /\
                                      In (job_task j) ts).
    intro LISTtsk; des; exists l; split.
      by intro INj; apply LISTtsk in INj; des.
      by rewrite LISTtsk; split; eauto.

  specialize (UNIQUE t); clear ARRts.
  induction ts as [| tsk1]; ins; des.
    (* Base Case *)
    by exists nil; split; ins; des; trivial.
    (* Inductive step *)
    destruct (classic (exists j, arrives_at sched j t /\
                       job_task j = tsk1)) as [ARRtsk1 | NOTARRtsk1]; des.
    {
      exists (j :: l); ins.
      split; ins; des; subst.
        by split; eauto.
        by rewrite IHts in H; des; eauto.
        by left; eauto.
        by right; rewrite IHts; split; eauto.
    }
    {
      exists l; split; ins; des; subst.
        by rewrite IHts in H; des; eauto.
        by exfalso; apply NOTARRtsk1; exists j; eauto.
        by rewrite IHts; eauto.
    }
Qed.
         
Lemma ts_finite_arrival_sequence:
  forall ts sched (ARRts: ts_arrival_sequence ts sched)
         (UNIQUE: task_job_unique sched) (t: time),
    exists (l: list job), arrival_list sched l t.
Proof.
  unfold ts_arrival_sequence, arrival_list, arrived; ins.
  assert (ARR:= released_jobs_at ts sched ARRts UNIQUE).
  induction t as [| t ARRbefore].
  {
    specialize (ARR 0); des.
    exists l; ins; split; intro H; des.
      by exists 0; split; [trivial |]; apply ARR; eauto.
      by red; assert (t_0 = 0); [omega |]; subst; apply ARR.
  }
  {
    destruct ARRbefore as [l_before ARRbefore].
    specialize (ARR (S t)); destruct ARR as [l_cur ARRcur].
    exists (l_before ++ l_cur); ins; split.
    {
      intro IN; apply in_app_or in IN; des.
        by rewrite ARRbefore in IN; des; exists t_0; split; eauto.
        by exists (S t); split; [trivial |]; rewrite <- ARRcur.
    }
    {
      intro BEFORE; des.
      apply in_or_app; inversion BEFORE; subst.
        by right; rewrite ARRcur.
        by left; rewrite ARRbefore; exists t_0; split.
    }
  }
Qed.

(* Sporadic arrival times for every task in a taskset.
   We use only '->' because the first arrival may be at any point. *)
Definition periodic_task_model (ts: taskset) (sched: schedule) :=
  << ARRts: ts_arrival_sequence ts sched >> /\
  forall j arr (ARRj: arrives_at sched j arr),
    exists (j': job) (arr': time), job_task j' = job_task j /\
                                   arrives_at sched j' arr' /\
                                   arr' = arr + task_period (job_task j).

(* Periodic arrival times *)
Definition sporadic_task_model (ts: taskset) (sched: schedule) :=
  << ARRts: ts_arrival_sequence ts sched >> /\
  forall j arr (ARRj: arrives_at sched j arr),
    exists (j': job) (arr': time), job_task j' = job_task j /\
                                   arrives_at sched j' arr' /\
                                   arr' >= arr + task_period (job_task j).

(* Synchronous release at time t *)
Definition sync_release (ts: taskset) (sched: schedule) (t: time) :=
  << ARRts: ts_arrival_sequence ts sched >> /\
  forall (tsk: sporadic_task) (IN: In tsk ts),
    exists (j: job), job_task j = tsk /\ arrives_at sched j t.