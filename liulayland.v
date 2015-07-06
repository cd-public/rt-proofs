Require Import List Arith Sorting Vbase job task schedule identmp priority helper response_time task_arrival.

Section LiuLayland.
Variable ts: taskset.
Variable sched: schedule.
Variable hp: higher_priority.
Variable cpumap: processor_list.

Definition task_hp := fp_higher_priority RM. (* Rate-monotonic priority *)
Hypothesis RM_priority : fixed_priority hp task_hp. (* Link job priority with task priority *)

Definition uniprocessor := ident_mp 1 hp cpumap. (* Uniprocessor system *)
Hypothesis platform : uniprocessor sched.

Hypothesis arr_seq_from_ts: ts_arrival_sequence ts sched. (* Arrival sequence from task set *)
Hypothesis periodic_tasks: periodic_task_model ts sched.
Hypothesis implicit_deadlines: implicit_deadline_model ts.

Hypothesis ts_non_empty: ts <> nil.
Hypothesis ts_sorted_by_prio: StronglySorted task_hp ts. 

Hypothesis job_cost_wcet: forall j t tsk (JOBj: job_of j = Some tsk) (ARRj: arrives_at sched j t), job_cost j = task_cost tsk.

(* Simpler scheduling invariant for uniprocessor (eliminates cpu mapping) *)
Lemma uni_simpler_invariant :
  forall jlow t, 
    backlogged sched jlow t <-> exists jhigh, hp sched t jhigh jlow /\ scheduled sched jhigh t.
Proof.
  rename platform into PLAT.
  unfold uniprocessor, ident_mp in *; split; intro BL; des; specialize (mp_invariant jlow t).
  {
    destruct mp_invariant as [mp_invariant _].
    apply mp_invariant with (cpu := 0) in BL; [| by eauto]; des.
    exists jhigh; split; [by eauto|].
    rewrite <- mp_mapping.
    eauto using element_in_list.
  }
  {
    destruct mp_invariant as [_ mp_invariant].
    apply mp_invariant; ins.
    exists jhigh; split; [by eauto|].
    apply In_singleton_list; eauto.
      by rewrite mp_mapping.
  }
Qed.

Lemma periodic_arrival_k_times : 
  forall j tsk (JOBj: job_of j = Some tsk) t (ARRj: arrives_at sched j t) k,
    exists j', << JOBj': job_of j' = Some tsk >> /\
               << ARRj': arrives_at sched j' (t + k*(task_period tsk)) >>.
Proof.
  revert periodic_tasks; unfold periodic_task_model; intros PER; ins.
  specialize (PER arr_seq_from_ts).
  induction k; simpl; des.
    by rewrite <- plus_n_O; eauto.
    {
      apply PER with (t := t + k*(task_period tsk)) in JOBj'; eauto; des; subst.
      exists j'0; split; eauto.
      assert (COMM : t + k * task_period tsk + task_period tsk =
                     t + (task_period tsk + k * task_period tsk)); [by omega |].
      rewrite <- COMM; trivial.
    }
Qed.

Lemma sync_release_is_critical_instant :
  forall t tsk_i (INi: In tsk_i ts) (SYNC: sync_release ts sched t),
    critical_instant uniprocessor tsk_i ts sched t.
Proof.
  revert ts_sorted_by_prio; intro SORTED.
  unfold sync_release, critical_instant; ins.
  assert (ARRi := SYNC tsk_i INi); des.
  exists j; repeat (split; eauto); ins.
  unfold task_response_time_ub. intros _ sched' j' t' r'; ins.

  inversion SORTED; subst.
    by intuition.
    


Lemma hp_task_no_interference :
    forall (tsk_i: sporadic_task),
        Forall (task_hp tsk_i) ts ->
            task_response_time tsk_i (tsk_i :: ts) (task_cost tsk_i).
Proof.
    intros tsk_i tsk_i_hp.
    unfold task_response_time.
    split. simpl. apply or_introl. trivial.
    generalize sched.
    clear periodic_tasks arr_seq_from_ts uniprocessor sched.
    intros sched uniprocessor arr_seq_from_ts periodic_tasks.


End LiuLayland.
