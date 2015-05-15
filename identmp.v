Require Import Coq.Lists.List.
Require Import job.
Require Import schedule.
Require Import priority.
Require Import platform.

(* Mapping from processors to tasks at time t *)
Definition processor_list := schedule -> time -> list (option job).

(* Whether a schedule is produced by an identical multiprocessor *)
Record ident_mp (num_cpus: nat) (hp: higher_priority)
                (cpumap: processor_list) (sched: schedule) : Prop :=
  { (* An identical multiprocessor has a fixed number of cpus *)
    ident_mp_cpus_nonzero: num_cpus > 0;
    ident_mp_num_cpus: forall (t: time), length (cpumap sched t) = num_cpus;

    (* Job is scheduled iff it is mapped to a processor*)
    ident_mp_mapping: forall (j: job) (t: time),
                          List.In (Some j) (cpumap sched t)
                              <-> scheduled sched j t;

    (* A job receives at most 1 unit of service *)
    ident_mp_sched_unit: forall (j: job) (t: time), service_at sched j t <= 1;

    (* Global scheduling invariant *)
    ident_mp_invariant:
        forall (jlow: job) (t: time),
            backlogged sched jlow t <->
                (forall (cpu: nat),
                cpu < num_cpus ->
                    (exists (jhigh: job),
                        hp sched t jhigh jlow
                        /\ (nth cpu (cpumap sched t) None = Some jhigh)))
  }.

Lemma highest_prio_no_interference :
    forall (tsk_i: sporadic_task),
        (forall (sched' : schedule) (task_hp: sporadic_task->sporadic_task->Prop),
            ident_mp num_cpus  sched' ->
            ts_arrival_sequence (tsk_i :: ts) sched' ->
            fixed_priority hp task_hp ->
            Forall (task_hp tsk_i) ts ) ->
        task_response_time_max uniprocessor tsk_i (tsk_i :: ts) (task_cost tsk_i).
Proof.
    intros tsk_i H.
    unfold task_response_time_max. split.
    - unfold task_response_time_ub. split. simpl. apply or_introl. trivial.
      intros  j t_a r plat arr_seq_of_j job_of_j arr_j resp_time_j.
      unfold job_response_time in resp_time_j.
      specialize (resp_time_j t_a arr_j).
      unfold least_nat in resp_time_j.
      inversion resp_time_j as [completed_j first_time_completed_j].
      apply first_time_completed_j.
      unfold completed.
      split.
        + assert (tsk_i_cost_positive := task_cost_positive tsk_i).
          destruct (task_cost tsk_i). inversion tsk_i_cost_positive.
          rewrite <- plus_n_Sm. apply gt_Sn_O.

        + (* Prove that tsk_i has service = e_i, by induction on t *)
          assert (always_scheduled : forall t, service sched j (t_a + t) = t + 1).
          induction t.
            * rewrite <- plus_n_O. simpl.
              destruct t_a as [a | t_0]. simpl.
                  admit.
              simpl.
              rewrite (not_arrived_no_service sched j (S t_0) arr_j t_0).
              simpl.


inversion S_t_0_less.
        assert (H2 := le_Sn_n t_0).
        assert (H3 := le_refl t_0).
        omega. inversion H0.

              unfold service.
              destruct (t < t_a).
          induction (t_a + task_cost tsk_i - 1).
       

    Admitted.(*

Lemma highest_prio_no_interference :
    forall (ts: taskset)(tsk_i: sporadic_task),
        (forall (sched : schedule) (task_hp: sporadic_task->sporadic_task->Prop),
            platform sched ->
            ts_arrival_sequence (tsk_i :: ts) sched ->
            fixed_priority hp task_hp ->
            Forall (task_hp tsk_i) ts ) ->
        task_response_time_max tsk_i (tsk_i :: ts) (task_cost tsk_i).
Proof.

*)