Require Import List Arith Sorting Vbase job task schedule identmp priority helper response_time task_arrival.

Section LiuLayland.
Variable ts: taskset.
Variable sched: schedule.
Variable hp: sched_job_hp_relation.
Variable cpumap: job_mapping.

Hypothesis RM_priority : convert_fp_jldp RM hp.

Definition uniprocessor := ident_mp 1 hp cpumap. (* Uniprocessor system *)
Hypothesis platform : uniprocessor sched.

Hypothesis arr_seq_from_ts: ts_arrival_sequence ts sched. (* Arrival sequence from task set *)
Hypothesis periodic_tasks: periodic_task_model ts sched.
Hypothesis implicit_deadlines: implicit_deadline_model ts.

Hypothesis ts_non_empty: ts <> nil.
Hypothesis ts_sorted_by_prio: StronglySorted RM ts. 

Hypothesis job_cost_wcet: forall j t tsk (JOBj: job_task j = tsk) (ARRj: arrives_at sched j t), job_cost j = task_cost tsk.

Lemma periodic_arrival_k_times : 
  forall j tsk (JOBj: job_task j = tsk) t (ARRj: arrives_at sched j t) k,
    exists j', << JOBj': job_task j' = tsk >> /\
               << ARRj': arrives_at sched j' (t + k*(task_period tsk)) >>.
Proof.
  revert periodic_tasks; unfold periodic_task_model; intros PER; ins; des.
  induction k; simpl; des.
    by rewrite <- plus_n_O; eauto.
    {
      apply PER0 in ARRj'; des; subst; rewrite JOBj' in *.
      exists j'0; split; eauto using eq_trans.
      assert (COMM : t + k * task_period (job_task j) + task_period (job_task j) =
                     t + (task_period (job_task j) + k * task_period (job_task j))); [by omega |].
      rewrite <- COMM; trivial.
    }
Qed.

(*Lemma sync_release_is_critical_instant :
  forall t tsk_i (INi: In tsk_i ts) (SYNC: sync_release ts sched t),
    critical_instant uniprocessor tsk_i ts sched t.
Proof.
Admitted.

Lemma hp_task_no_interference :
    forall (tsk_i: sporadic_task),
        Forall (task_hp tsk_i) ts ->
            task_response_time tsk_i (tsk_i :: ts) (task_cost tsk_i).
Proof.
Admitted.*)

End LiuLayland.
