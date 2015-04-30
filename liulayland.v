Add LoadPath "/home/felipec/dev/coq/rt-scheduling-spec".
Require Import Coq.Lists.List.
Require Import Coq.Arith.Lt.
Require Import job.
Require Import task.
Require Import schedule.
Require Import identmp.
Require Import priority.
Require Import helper.

Section LiuLayland.
Variable ts: taskset.
Variable sched: schedule.
Variable hp: higher_priority.
Variable task_hp (tsk1: sporadic_task) (tsk2: sporadic_task): fp_higher_priority RM.
Variable cpumap: processor_list.

Hypothesis RM_priority : fixed_priority hp RM. (* Rate-monotonic priority *)
Hypothesis uniprocessor : ident_mp 1 sched hp cpumap. (* Uniprocessor system *)
Hypothesis jobs_from_taskset: schedule_of_taskset sched ts. (* All jobs come from task set *)
Hypothesis arr_seq_from_ts: ts_arrival_sequence ts (arr_seq sched). (* Arrival sequence from task set *)
Hypothesis periodic_tasks: periodic_task_model ts (arr_seq sched).
Hypothesis implicit_deadlines: implicit_deadline_model ts.

Definition hp_task (tsk1 tsk2: sporadic_task) := fp_higherprio RM tsk1 tsk2.

(* Simpler scheduling invariant for uniprocessor (eliminates cpu mapping) *)
Lemma uni_simpler_invariant :
      forall (jlow : job) (t : time),
          backlogged sched jlow t
              <-> exists jhigh : job, hp jhigh jlow sched t /\ scheduled sched jhigh t.
Proof.
  intros.
  assert (H1 := uniprocessor).
  split.
  intros.
  inversion H1.
  assert (H3 := ident_mp_invariant jlow t).
  inversion H3 as [H4 _]. clear H3 ident_mp_invariant ident_mp_cpus_nonzero.
  edestruct ((H4 H) 0) as [jhigh H5]. apply le_lt_n_Sm. trivial.
  inversion H5 as [H6 H7].
  assert (H8 := element_in_list job jhigh (cpumap sched t) 0 H7).
  exists jhigh.
  specialize (ident_mp_mapping jhigh t).
  inversion ident_mp_mapping as [H9 _].
  apply H9 in H8.
  apply (conj H6 H8).
  
  intros. inversion H as [jhigh]. inversion H0.
  inversion H1.
  specialize (ident_mp_invariant jlow t).
  inversion ident_mp_invariant as [_ H4].
  apply H4.
  intros. exists jhigh. split. apply H2.
  specialize (ident_mp_mapping jhigh t).
  inversion ident_mp_mapping as [_ H6].
  specialize (H6 H3).
  apply In_singleton_list with (x := jhigh); trivial.
Qed.

Lemma bla : forall (t: time) (tsk_i),
                (forall (hp_tsk: sporadic_task),
                In tsk ts ->
                exists (j: job), (arr_seq sched) j t)
                    -> critical_instant tsk sched t.

End LiuLayland.