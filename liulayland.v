Require Import Coq.Lists.List.
Require Import Coq.Arith.Lt.
Require Import job.
Require Import task.
Require Import schedule.
Require Import identmp.
Require Import priority.
Require Import helper.
Require Import response_time.
Require Import task_arrival.
Require Import Coq.Program.Tactics.
Require Import Omega.
Require Import Coq.Sorting.Sorted.

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

Hypothesis ts_non_empty: ts <> nil. (* TODO: make this a global assumption? *)
Hypothesis ts_sorted_by_prio: StronglySorted task_hp ts. 

(* Simpler scheduling invariant for uniprocessor (eliminates cpu mapping) *)
Lemma uni_simpler_invariant :
      forall (jlow : job) (t : time),
          backlogged sched jlow t
              <-> exists jhigh : job, hp sched t jhigh jlow /\ scheduled sched jhigh t.
Proof.
  intros.
  split.
  - intros.
    inversion platform.
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
  
  - intros. inversion H as [jhigh]. inversion H0.
    inversion platform.
    specialize (ident_mp_invariant jlow t).
    inversion ident_mp_invariant as [_ H4].
    apply H4.
    intros. exists jhigh. split. apply H1.
    specialize (ident_mp_mapping jhigh t).
    inversion ident_mp_mapping as [_ H6].
    specialize (H6 H2).
    apply In_singleton_list with (x := jhigh); trivial.
Qed.

Lemma periodic_arrival_k_times : 
    forall (j: job) (t: time) (tsk: sporadic_task), 
        job_of j = Some tsk ->
        arrives_at sched j t ->
        forall k, exists (j': job), job_of j' = Some tsk
                                    /\ arrives_at sched j' (t + k*(task_period tsk)).
Proof.
    intros j t tsk job_of_j j_arrival k.
    unfold periodic_task_model in periodic_tasks.
    specialize (periodic_tasks arr_seq_from_ts).

    induction k.
        - simpl. rewrite <- plus_n_O.
          exists j. split; trivial.
        - simpl. inversion IHk as [j' [job_of_j' j'_arrival]].
          specialize (periodic_tasks tsk j' (t + k*(task_period tsk))).
          specialize (periodic_tasks (conj job_of_j' j'_arrival)).
          inversion periodic_tasks as [j'' [t'' [H1 [H2 H3]]]].
          subst t''.
          exists j''. split. trivial.
          assert (H : t + k * task_period tsk + task_period tsk =
                           t + (task_period tsk + k * task_period tsk)). omega.
          rewrite <- H.
          apply H2.
Qed.

Lemma sync_release_is_critical_instant :
    forall (t: time) (tsk_i: sporadic_task),
        In tsk_i ts ->
        sync_release ts sched t ->
        critical_instant uniprocessor tsk_i ts sched t.
Proof.
    intros t tsk_i tsk_i_in_ts synchronous_release.
    unfold sync_release in synchronous_release.
    assert (tsk_i_arrives := synchronous_release tsk_i tsk_i_in_ts).
    inversion_clear tsk_i_arrives as [j_i [job_of_tsk_i arrival_tsk_i]].
    unfold critical_instant.
    exists j_i. do 2 (split; trivial).
    intros r resptime_j_r.

    unfold task_response_time_ub.
    split. trivial.
    intros sched0 j0 r0 platform_sched0 arr_seq_from_ts_j0 job_of_j0 resp_time_j0.
    
    assert (H := ts_sorted_by_prio). (* HACK: Coq cannot do induction on Hypothesis. *)
    induction H as [ts' | tsk_1 ts'].
      - contradiction ts_non_empty; trivial. (* Ignore empty taskset *)
      - destruct tsk_i_in_ts. 
        + (* If tsk_i = tsk_1 *)
          subst tsk_i.
        + (* Else, tsk_i in ts' *)


apply IHStronglySorted.
        destruct tsk_i_first_or_cons as [tsk_i_first | tsk_i_cons]. 
          + intros job_of_tsk_i. subst tsk_i.

            (* Need a lemma here... *)
            unfold task_response_time.
            split. simpl. apply or_introl. trivial.
            



    revert ts_non_empty.
    elim ts.
    destruct ts as [ts | tsk_1 ts'].
        - contradiction ts_non_empty; trivial. (* Ignore empty taskset *)
        - elim ts_sorted_by_prio. (* Induction on the sorted task set *)
          inversion ts_sorted_by_prio as [tmp1 | tmp1 tmp2 ts'_sorted_by_prio tsk_1_hp tmp5].
          subst tmp1 tmp2.

    elim ts_sorted_by_prio.
    destruct ts as [ts | tsk_1 ts'].
    - contradiction ts_non_empty; trivial. (* Ignore empty taskset *)
    -

 inversion ts_sorted_by_prio as [x1 | x1 x2 x3]. subst a l.
          induction 

induction s.
    elim ts_sorted_by_prio.

    assert (H := periodic_arrival_k_times).
    
    unfold job_response_time.
    intros t_a tsk_i_arr_ta.

    (* Prove that t_a = t and eliminate duplicates *)
    assert (t_a_equals_t := no_multiple_arrivals (arrives_at sched)).
    specialize (t_a_equals_t j_i t t_a tsk_i_arr tsk_i_arr_ta).
    subst t_a. clear_dups.

    unfold least_nat. split.
    unfold task_response_time in response_time.
    inversion_clear response_time as [_ r_largest_job_response_time].
    specialize (r_largest_job_response_time sched j_i arr_seq_from_ts job_tsk_i).
    inversion_clear r_largest_job_response_time as [r_job_response_time _].
    unfold job_response_time in r_job_response_time.
    specialize (r_job_response_time t tsk_i_arr).
    inversion r_job_response_time. trivial.


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
