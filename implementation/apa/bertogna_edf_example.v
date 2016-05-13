Require Import rt.util.all.
Require Import rt.model.apa.job rt.model.apa.task rt.model.apa.affinity
               rt.model.apa.schedule rt.model.apa.interference
               rt.model.apa.schedulability
               rt.model.apa.priority rt.model.apa.platform.
Require Import rt.analysis.apa.workload_bound
               rt.analysis.apa.interference_bound_edf
               rt.analysis.apa.bertogna_edf_comp.
Require Import rt.implementation.apa.job
               rt.implementation.apa.task
               rt.implementation.apa.schedule
               rt.implementation.apa.arrival_sequence.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq fintype bigop div.

Module ResponseTimeAnalysisEDF.

  Import Job Schedule SporadicTaskset Priority Schedulability
         Affinity Platform InterferenceBoundEDF WorkloadBound
         Interference ResponseTimeIterationEDF.
  Import ConcreteJob ConcreteTask ConcreteArrivalSequence ConcreteScheduler.

  (* In this section, we instantiate a simple example to show that the theorems
     contain no contradictory assumptions. *)
  Section ExampleRTA.

    (* Assume there are two processors. *)
    Let num_cpus := 2.

    (* Let (cpu j) denote the j-th processor *)
    Let cpu j := @Ordinal num_cpus j.

    (* Define alpha1 := {cpu 0, cpu 1} with the two processors. *)
    Program Let alpha1 : affinity num_cpus :=
      (Build_set [:: cpu 0 _; cpu 1 _] _).

    (* Define the singleton affinity alpha2 := {cpu 0}. *)
    Program Let alpha2 : affinity num_cpus :=
      (Build_set [:: cpu 0 _] _).

    (* Define the singleton affinity alpha3 := {cpu 1}. *)
    Program Let alpha3 : affinity num_cpus :=
      (Build_set [:: cpu 1 _] _).

    (* Now we create three tasks using the affinities above ... *)
    Let tsk1 := {| task_id := 1; task_cost := 3; task_period := 5;
                   task_deadline := 3; task_affinity := alpha1|}.
    Let tsk2 := {| task_id := 2; task_cost := 2; task_period := 6;
                   task_deadline := 5; task_affinity  := alpha2|}.
    Let tsk3 := {| task_id := 3; task_cost := 2; task_period := 12;
                   task_deadline := 11; task_affinity := alpha3|}.

    (* ... and group these tasks into task set ts. *)
    Program Let ts := Build_set [:: tsk1; tsk2; tsk3] _.

    (* In this section, we let Coq compute a few properties about ts. *)
    Section FactsAboutTaskset.

      (* There are no empty affinities. *)
      Fact ts_non_empty_affinities:
        forall tsk, 
          tsk \in ts ->
          #|task_affinity tsk| > 0.
      Proof.
        intros tsk IN.
        by repeat (move: IN => /orP [/eqP EQ | IN]; subst; rewrite ?set_card; compute).
      Qed.

      (* The tasks have valid parameters (e.g., cost > 0). *)
      Fact ts_has_valid_parameters:
        valid_sporadic_taskset task_cost task_period task_deadline ts.
      Proof.
        intros tsk IN.
        by repeat (move: IN => /orP [/eqP EQ | IN]; subst; compute).
      Qed.

      (* The task set has constrained deadlines. *)
      Fact ts_has_constrained_deadlines:
        forall tsk,
          tsk \in ts ->
          task_deadline tsk <= task_period tsk.
      Proof.
        intros tsk IN.
        by repeat (move: IN => /orP [/eqP EQ | IN]; subst; compute).
      Qed.

    End FactsAboutTaskset.

    (* Next, recall the EDF RTA schedulability test for APA scheduling.
       Note that the task functions (from implementation/apa/task.v)
       require num_cpus as a parameter, so we leave a blank space so that
       can be inferred automatically. *)
    Let schedulability_test :=
      edf_schedulable (@task_cost _) (@task_period _)
                      (@task_deadline _) num_cpus task_affinity
                      task_affinity. (* For simplicity, we use subaffinity alpha' = alpha. *)

    (* Now, we guide Coq to compute the schedulability test function
       and show it returns true. *)
    Fact schedulability_test_succeeds :
      schedulability_test ts = true.
    Proof.
      unfold schedulability_test, edf_schedulable, edf_claimed_bounds; desf.
      apply negbT in Heq; move: Heq => /negP ALL.
      exfalso; apply ALL; clear ALL.
      assert (STEPS: \sum_(tsk <- ts) (task_deadline tsk - task_cost tsk) + 1 = 13).
      {
        by rewrite unlock; compute.
      } rewrite STEPS; clear STEPS.

      have cpu0P: 0 < 2 by done.
      have cpu1P: 1 < 2 by done.

      have cpu_compute :
        forall (P: processor num_cpus -> bool),
          [exists x, P x] =
            if (P (cpu 0 cpu0P)) then true else
              if P (cpu 1 cpu1P) then true else false.
      {
        unfold num_cpus in *; intros P.
        destruct (P (cpu 0 cpu0P)) eqn:P0;
          first by apply/existsP; exists (cpu 0 cpu0P).
        destruct (P (cpu 1 cpu1P)) eqn:P1;
          first by apply/existsP; exists (cpu 1 cpu1P).
        apply negbTE; rewrite negb_exists; apply/forallP.
        intros x; destruct x as [x LE]; apply negbT.
        have GE0 := leq0n x.
        rewrite leq_eqVlt in GE0; move: GE0 => /orP [/eqP EQ0 | GE1];
          first by rewrite -P0; f_equal; apply ord_inj.
        rewrite leq_eqVlt in GE1; move: GE1 => /orP [/eqP EQ1 | GE2];
          first by rewrite -P1; f_equal; apply ord_inj.
        have LE' := LE.
        apply leq_ltn_trans with (m := 2) in LE'; last by done.
        by rewrite ltnn in LE'.
      }

      Ltac f :=
        unfold edf_rta_iteration; simpl;
        unfold edf_response_time_bound, div_floor, total_interference_bound_edf, interference_bound_edf, interference_bound_generic, W, edf_specific_interference_bound, different_task_in, affinity_intersects; simpl;
        rewrite !addnE !set_card !big_cons ?big_nil /=.

      
      rewrite [edf_rta_iteration]lock; simpl.
      unfold locked at 13; destruct master_key; f; rewrite !cpu_compute /=.
      unfold locked at 12; destruct master_key; f; rewrite !cpu_compute /=.
      unfold locked at 11; destruct master_key; f; rewrite !cpu_compute /=.
      unfold locked at 10; destruct master_key; f; rewrite !cpu_compute /=.
      unfold locked at 9; destruct master_key; f; rewrite !cpu_compute /=.
      unfold locked at 8; destruct master_key; f; rewrite !cpu_compute /=.
      unfold locked at 7; destruct master_key; f; rewrite !cpu_compute /=.
      unfold locked at 6; destruct master_key; f; rewrite !cpu_compute /=.
      unfold locked at 5; destruct master_key; f; rewrite !cpu_compute /=.
      unfold locked at 4; destruct master_key; f; rewrite !cpu_compute /=.
      unfold locked at 3; destruct master_key; f; rewrite !cpu_compute /=.
      unfold locked at 2; destruct master_key; f; rewrite !cpu_compute /=.
      by unfold locked at 1; destruct master_key; f; rewrite !cpu_compute /=.
    Qed.

    (* Let arr_seq be the periodic arrival sequence from ts. *)
    Let arr_seq := periodic_arrival_sequence ts.

    (* Let sched be the weak APA EDF scheduler. *)
    Let sched := scheduler job_cost job_task num_cpus arr_seq task_affinity (EDF job_deadline).

    (* Recall the definition of deadline miss. *)
    Let no_deadline_missed_by :=
      task_misses_no_deadline job_cost job_deadline job_task sched.

    (* To show that the RTA works, we infer the schedulability of the task
       set from the result of the RTA procedure. *)
    Corollary ts_is_schedulable:
      forall tsk,
        tsk \in ts ->
        no_deadline_missed_by tsk.
    Proof.
      intros tsk IN.
      have VALID := periodic_arrivals_valid_job_parameters ts ts_has_valid_parameters.
      have VALIDTS := ts_has_valid_parameters.
      unfold valid_sporadic_job, valid_realtime_job in *; des.
      apply taskset_schedulable_by_edf_rta with (task_cost := task_cost) (task_period := task_period) (task_deadline := task_deadline) (alpha := task_affinity) (alpha' := task_affinity) (ts0 := ts).
      - by apply ts_has_valid_parameters. 
      - by apply ts_has_constrained_deadlines.
      - by apply ts_non_empty_affinities.
      - by ins.
      - by apply periodic_arrivals_all_jobs_from_taskset.
      - by apply periodic_arrivals_valid_job_parameters, ts_has_valid_parameters.
      - by apply periodic_arrivals_are_sporadic.
      - by apply scheduler_jobs_must_arrive_to_execute.
      - apply scheduler_completed_jobs_dont_execute; intro j'.
        -- by specialize (VALID j'); des.
        -- by apply periodic_arrivals_is_a_set.
      - by apply scheduler_sequential_jobs, periodic_arrivals_is_a_set.
      - by apply scheduler_respects_affinity.
      - apply scheduler_apa_work_conserving; try (by done).
        -- by apply periodic_arrivals_is_a_set.
        -- by apply EDF_is_transitive.
        -- by apply EDF_is_total.
      - apply scheduler_enforces_policy.
        -- by apply periodic_arrivals_is_a_set.
        -- by apply EDF_is_transitive.
        -- by apply EDF_is_total.
      - by apply schedulability_test_succeeds.
      - by apply IN.
    Qed.

  End ExampleRTA.

End ResponseTimeAnalysisEDF.