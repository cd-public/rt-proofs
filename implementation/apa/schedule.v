Require Import rt.util.all.
Require Import rt.model.arrival_sequence rt.model.job rt.model.task rt.model.priority
               rt.model.task_arrival.
Require Import rt.model.global.basic.schedule.
Require Import rt.model.apa.affinity rt.model.apa.platform.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat fintype bigop seq path.

Module ConcreteScheduler.

  Import Job SporadicTaskset ArrivalSequence Schedule Platform
         Priority Affinity.

  (* In this section, we implement a concrete weak APA scheduler. *)
  Section Implementation.
    
    Context {Job: eqType}.
    Context {sporadic_task: eqType}.
    
    Variable job_cost: Job -> time.
    Variable job_task: Job -> sporadic_task.

    (* Let num_cpus denote the number of processors, ...*)
    Variable num_cpus: nat.

    (* ... and let arr_seq be any arrival sequence.*)
    Variable arr_seq: arrival_sequence Job.

    (* Let alpha be an affinity associated with each task. *)
    Variable alpha: task_affinity sporadic_task num_cpus.
    
    (* Assume a JLDP policy is given. *)
    Variable higher_eq_priority: JLDP_policy arr_seq.

    (* Consider the list of pending jobs at time t, ... *)
    Definition jobs_pending_at (sched: schedule num_cpus arr_seq) (t: time) :=
      [seq j <- jobs_arrived_up_to arr_seq t | pending job_cost sched j t].

    (* ... which we sort by decreasing priority. *)
    Definition sorted_pending_jobs (sched: schedule num_cpus arr_seq) (t: time) :=
      sort (higher_eq_priority t) (jobs_pending_at sched t).

    (* Now we implement the algorithm that generates the APA schedule. *)
    
    (* Given a job j at time t, we first define a predicate that states
       whether j should preempt a mapping (cpu, x), where x is either Some j'
       that is currently mapped to cpu or None. *)
      Definition should_be_scheduled (j: JobIn arr_seq) (t: time) p :=
      let '(cpu, mapped_job) := p in
        if mapped_job is Some j' then (* If there is a job j', check the priority and affinity. *)
          (can_execute_on alpha (job_task j) cpu) &&
          ~~ (higher_eq_priority t j' j)
        else (* Else, if cpu is idle, check only the affinity. *)
          (can_execute_on alpha (job_task j) cpu).
    
    (* Next, using the "should_be_scheduled" predicate, we define a function
       that tries to schedule job j by updating a list of mappings.
       It does so by replacing the first pair (cpu, x) where j can be
       scheduled (if it exists). *)
    Definition update_available_cpu t allocation j :=
      replace_first (should_be_scheduled j t) (* search for processors that j can preempt *)
                    (set_pair_2nd (Some j)) (* replace the mapping in that processor with j *)
                    allocation. (* list of mappings *)

    (* Using the fuction "update_available_cpu", we now define an iteration
       that tries to successively schedule each job in a list job_list.
       Starting with an empty mapping,
       <(cpu0, None), (cpu1, None), (cpu2, None), ...>,
       it tries to schedule each job in job_list and yields some updated list: 
       <(cpu0, None), (cpu1, Some j5), (cpu2, j9), ...>. *)
    Definition try_to_schedule_every_job job_list t :=
      foldl (update_available_cpu t)
            (zip (enum (processor num_cpus)) (nseq num_cpus None)) (* empty mapping*)
            job_list.

    (* The iteration we just defined is then applied to the list of pending jobs
       at any time t. *)
    Definition schedule_every_pending_job prev_sched t :=
      try_to_schedule_every_job (sorted_pending_jobs prev_sched t) t.

    (* The schedule can now be constructed iteratively. Starting from the empty schedule, ... *)
    Definition empty_schedule : schedule num_cpus arr_seq :=
      fun cpu t => None.

    (* ..., we update the schedule at time t by calling schedule_every_pending_job with
       the list of pending jobs at time t, and then converting the result to a function. *)
    Definition update_schedule (prev_sched: schedule num_cpus arr_seq)
                               (t_next: time) : schedule num_cpus arr_seq :=
      fun cpu t =>
        if t == t_next then
          pairs_to_function None (schedule_every_pending_job prev_sched t) cpu
        else prev_sched cpu t.
    
    (* This allows us to iteratively construct the schedule up to some time t_max. *)
    Fixpoint schedule_prefix (t_max: time) : schedule num_cpus arr_seq := 
      if t_max is t_prev.+1 then
        (* At time t_prev + 1, schedule jobs that have not completed by time t_prev. *)
        update_schedule (schedule_prefix t_prev) t_prev.+1
      else
        (* At time 0, schedule any jobs that arrive. *)
        update_schedule empty_schedule 0.

    (* Finally, the prefixes are used to build the complete schedule. *)
    Definition scheduler (cpu: processor num_cpus) (t: time) := (schedule_prefix t) cpu t.

  End Implementation.

  (* In this section, we prove several properties about the scheduling algorithm we
     implemented. For example, we show that it is APA work conserving. *)
  Section Proofs.

    Context {Job: eqType}.
    Context {sporadic_task: eqType}.
    
    Variable job_cost: Job -> time.
    Variable job_task: Job -> sporadic_task.

    (* Assume a positive number of processors. *)
    Variable num_cpus: nat.
    Hypothesis H_at_least_one_cpu: num_cpus > 0.

    (* Let alpha be an affinity associated with each task. *)
    Variable alpha: task_affinity sporadic_task num_cpus.
    
    (* Let arr_seq be any arrival sequence of jobs where ...*)
    Variable arr_seq: arrival_sequence Job.
    (* ...jobs have positive cost and...*)
    Hypothesis H_job_cost_positive:
      forall (j: JobIn arr_seq), job_cost_positive job_cost j.
    (* ... at any time, there are no duplicates of the same job. *)
    Hypothesis H_arrival_sequence_is_a_set :
      arrival_sequence_is_a_set arr_seq.

    (* Consider any JLDP policy higher_eq_priority that is transitive and total. *)
    Variable higher_eq_priority: JLDP_policy arr_seq.
    Hypothesis H_priority_transitive: forall t, transitive (higher_eq_priority t).
    Hypothesis H_priority_total: forall t, total (higher_eq_priority t).
    
    (* Let sched denote our concrete scheduler implementation. *)
    Let sched := scheduler job_cost job_task num_cpus arr_seq alpha higher_eq_priority.
    
    (* Next, we provide some helper lemmas about the scheduler construction. *)
    Section HelperLemmas.

      (* Let sched_prefix denote the prefix construction of our scheduler. *)
      Let sched_prefix := schedule_prefix job_cost job_task num_cpus arr_seq alpha higher_eq_priority.

      (* We begin by showing that the scheduler preserves its prefixes. *)
      Lemma scheduler_same_prefix :
        forall t t_max cpu,
          t <= t_max ->
          sched_prefix t_max cpu t = sched cpu t.
      Proof.
        intros t t_max cpu LEt.
        induction t_max; first by rewrite leqn0 in LEt; move: LEt => /eqP EQ; subst.
        {
          rewrite leq_eqVlt in LEt.
          move: LEt => /orP [/eqP EQ | LESS]; first by subst.
          {
            feed IHt_max; first by done.
            unfold sched_prefix, schedule_prefix, update_schedule at 1.
            assert (FALSE: t == t_max.+1 = false).
            {
              by apply negbTE; rewrite neq_ltn LESS orTb.
            } rewrite FALSE.
            by rewrite -IHt_max.
          }
        }
      Qed.

      (* To avoid many parameters, let's also rename the scheduling function.
         We make a generic version (for any list of jobs l), ... *)
      Let schedule_jobs t l := try_to_schedule_every_job job_task num_cpus arr_seq alpha higher_eq_priority t l.
      (* ... and a specific version (for the pending jobs in sched). *)
      Let schedule_pending_jobs t := schedule_jobs (sorted_pending_jobs job_cost num_cpus arr_seq higher_eq_priority sched t) t.

      (* Next, we show that there are no duplicate cpus in the mapping. *)
      Lemma scheduler_uniq_cpus :
        forall t l,
          uniq (unzip1 (schedule_jobs l t)).
      Proof.
        intros t l.
        induction l as [| l' j_last] using last_ind.
        {
          by rewrite unzip1_zip; [rewrite enum_uniq | rewrite size_enum_ord size_nseq].
        }
        {
          rewrite /schedule_jobs /try_to_schedule_every_job -cats1 foldl_cat /=.
          assert (EQ: forall l j, unzip1 (update_available_cpu job_task num_cpus arr_seq
                                                alpha higher_eq_priority t l j) = unzip1 l).
          {
            intros l j; clear -l j.
            induction l; first by done.
            unfold update_available_cpu; simpl.
            by case SHOULD: should_be_scheduled; simpl; f_equal.
          }
          by rewrite EQ.
        }
      Qed.

      (* Next, we show that if a job j is in the mapping, then j must come from the list
         of jobs l used in the construction. *)
      Lemma scheduler_job_in_mapping :
        forall l j t cpu,
          (cpu, Some j) \in schedule_jobs l t -> j \in l.
      Proof.
        intros l j t cpu SOME; clear -SOME.
        unfold schedule_every_pending_job in *.
        induction l as [| l' j'] using last_ind; simpl in *.
        {
          apply mem_zip in SOME; last by rewrite size_enum_ord size_nseq.
          by move: SOME => [_ /nseqP [SOME _]].
        }
        {
          rewrite /schedule_jobs /try_to_schedule_every_job -cats1 foldl_cat /= in SOME.
          unfold update_available_cpu in SOME.
          elim (replace_first_cases SOME) => [IN | [y [NEW IN]]].
          {
            by rewrite mem_rcons in_cons; apply/orP; right; apply IHl.
          }
          {
            case: NEW => EQ1 EQ2; subst.
            by rewrite mem_rcons in_cons eq_refl orTb.
          }
        }
      Qed.

      (* Next, we prove that if a pair (cpu, j) is in the mapping, then
         cpu must be part of j's affinity. *)
      Lemma scheduler_mapping_respects_affinity :
        forall j t cpu,
          (cpu, Some j) \in schedule_pending_jobs t ->
          can_execute_on alpha (job_task j) cpu.
      Proof.
        intros j t cpu SOME.
        unfold schedule_pending_jobs, schedule_every_pending_job in SOME.
        set l := sorted_pending_jobs _ _ _ _ _ _ in SOME.
        induction l as [| l' j'] using last_ind; simpl in *.
        {
          apply mem_zip in SOME; last by rewrite size_enum_ord size_nseq.
          by move: SOME => [_ /nseqP [BUG _]].
        }
        {
          unfold schedule_jobs, try_to_schedule_every_job in SOME.
          rewrite -cats1 foldl_cat /= in SOME.
          elim (replace_first_cases SOME) => [IN | [y [NEW [SHOULD _]]]];
            first by apply IHl.
          case: NEW => EQ1 EQ2; subst.
          by unfold should_be_scheduled in SHOULD; desf.
        }
      Qed.

      (* Next, we show that the mapping does not schedule the same job j in two
         different cpus. *)
      Lemma scheduler_has_no_duplicate_jobs :
        forall j t cpu1 cpu2,
          (cpu1, Some j) \in schedule_pending_jobs t ->
          (cpu2, Some j) \in schedule_pending_jobs t ->
          cpu1 = cpu2.
      Proof.
        intros j t cpu1 cpu2 SOME1 SOME2.
        unfold schedule_pending_jobs, schedule_every_pending_job in *.
        set l := sorted_pending_jobs _ _ _ _ _ _ in SOME1 SOME2.
        assert (UNIQ: uniq l).
          by rewrite sort_uniq; apply filter_uniq, JobIn_uniq.
          
        induction l as [| l' j'] using last_ind; simpl in *.
        {
          apply mem_zip in SOME1; last by rewrite size_enum_ord size_nseq.
          by move: SOME1 => [_ /nseqP [BUG _]].
        }
        {
          rewrite rcons_uniq in UNIQ; move: UNIQ => /andP [NOTIN UNIQ].
          rewrite /schedule_jobs /try_to_schedule_every_job -cats1 foldl_cat /= in SOME1 SOME2.
          destruct (replace_first_cases SOME1) as [SAME1 | [[cpu1' p1] [EQ1 [SHOULD1 PREV1]]]];
          destruct (replace_first_cases SOME2) as [SAME2 | [[cpu2' p2] [EQ2 [SHOULD2 PREV2]]]].
          {
            by apply IHl.
          }
          {
            move: EQ2; case => EQ1 EQ2; subst cpu2' j'.
            destruct p2 as [j2 |].
            {
              apply scheduler_job_in_mapping in SAME1.
              by rewrite SAME1 in NOTIN.
            }
            by apply (replace_first_new _ _ _ (cpu2, Some j)) in SOME1;
              [by move: SOME1; case => -> | | | by done];
              apply/negP; intro BUG;
              apply scheduler_job_in_mapping in BUG;
              by rewrite BUG in NOTIN.
          }
          {
            move: EQ1; case => EQ1 EQ2; subst cpu1' j'.
            destruct p1 as [j1 |].
            {
              apply scheduler_job_in_mapping in SAME2.
              by rewrite SAME2 in NOTIN.
            }
            by apply (replace_first_new _ _ _ (cpu2, Some j)) in SOME1;
              [by move: SOME1; case => -> | | | by done];
              apply/negP; intro BUG;
              apply scheduler_job_in_mapping in BUG;
              by rewrite BUG in NOTIN.
          }
          {
            move: EQ1; case => /= EQ1' /= EQ2'; subst cpu1' j'.
            move: EQ2; case => EQ1'; subst cpu2'.
            by apply (replace_first_new _ _ _ (cpu2, Some j)) in SOME1;
              [by move: SOME1; case => -> | | | by done];
              apply/negP; intro BUG;
              apply scheduler_job_in_mapping in BUG;
              by rewrite BUG in NOTIN.
          }
        }
      Qed.

      (* Based on the definition of the schedule, a job j is scheduled on cpu
         iff (cpu, Some j) is the final mapping. *)
      Lemma scheduler_scheduled_on :
        forall j cpu t,
          scheduled_on sched j cpu t = ((cpu, Some j) \in schedule_pending_jobs t).
      Proof.
        unfold schedule_pending_jobs, schedule_jobs in *.
        intros j cpu t.
        induction t.
        {
          apply/idP/idP.
          {
            intros SCHED.
            unfold scheduled_on, sched, scheduler, schedule_prefix in SCHED.
            rewrite /update_schedule eq_refl in SCHED; move: SCHED => /eqP SCHED.
            apply pairs_to_function_neq_default in SCHED; last by done.
            unfold schedule_every_pending_job in SCHED.
            set l := sorted_pending_jobs _ _ _ _ _ _ in SCHED.
            set l' := sorted_pending_jobs _ _ _ _ _ _.
            assert (EQ: l' = l).
            {
              unfold l, l', sorted_pending_jobs; f_equal.
              unfold jobs_pending_at; apply eq_filter.
              unfold pending; red; intro j0; do 2 f_equal.
              unfold completed; f_equal.
              by unfold service; rewrite big_geq // big_geq //.
            }
            by rewrite EQ.
          }
          {
            intros SCHED.
            have MEM := pairs_to_function_mem None.
            apply MEM in SCHED; clear MEM; last by apply (scheduler_uniq_cpus 0).
            unfold scheduled_on, sched, scheduler, schedule_prefix.
            rewrite /update_schedule eq_refl.
            rewrite -SCHED; apply/eqP; f_equal.
            unfold schedule_pending_jobs, schedule_jobs, schedule_every_pending_job; f_equal.
            unfold sorted_pending_jobs, jobs_pending_at; f_equal.
            apply eq_filter; intros j0.
            unfold pending; do 2 f_equal.
            unfold completed; f_equal.
            by unfold service; rewrite big_geq // big_geq //.
          }
        }
        {
          apply/idP/idP.
          {
            intros SCHED.
            unfold scheduled_on, sched, scheduler, schedule_prefix in SCHED.
            rewrite /update_schedule eq_refl in SCHED; move: SCHED => /eqP SCHED.
            apply pairs_to_function_neq_default in SCHED; last by done.
            unfold schedule_every_pending_job in SCHED.
            set l := try_to_schedule_every_job _ _ _ _ _ _ _ in SCHED.
            set l' := try_to_schedule_every_job _ _ _ _ _ _ _.
            assert (EQ: l' = l).
            {
              unfold l', l, schedule_every_pending_job; f_equal.
              unfold sorted_pending_jobs, jobs_pending_at; f_equal.
              apply eq_filter; intros j0.
              unfold pending; do 2 f_equal.
              unfold completed; f_equal.
              unfold service. rewrite big_nat_recr // big_nat_recr //=.
              f_equal; apply eq_big_nat; intros t0 LE.
              unfold service_at; apply eq_bigl; intros cpu0.
              unfold scheduled_on; f_equal.
              unfold sched; move: LE => /andP [_ LE].
              by rewrite <- scheduler_same_prefix with (t_max := t); last by apply ltnW.
            }
            by rewrite EQ.
          }
          {
            intros SCHED.
            have MEM := pairs_to_function_mem None.
            apply MEM in SCHED; clear MEM; last by apply (scheduler_uniq_cpus t.+1).
            unfold scheduled_on, sched, scheduler, schedule_prefix.
            rewrite /update_schedule eq_refl.
            rewrite -SCHED; apply/eqP; f_equal.
            unfold schedule_every_pending_job; f_equal.
            unfold sorted_pending_jobs, jobs_pending_at; f_equal.
            apply eq_filter; intros j0.
            unfold pending; do 2 f_equal.
            unfold completed; f_equal.
            unfold service. rewrite big_nat_recr // big_nat_recr //=.
            f_equal; apply eq_big_nat; intros t0 LE.
            unfold service_at; apply eq_bigl; intros cpu0.
            unfold scheduled_on; f_equal.
            unfold sched; move: LE => /andP [_ LE].
            by rewrite <- scheduler_same_prefix with (t_max := t); last by apply ltnW.
          }  
        }
      Qed.

      (* Now we show that for every cpu, there is always a pair in the mapping. *)
      Lemma scheduler_has_cpus :
        forall cpu t l,
          exists x,
            (cpu, x) \in schedule_jobs l t. 
      Proof.
        intros cpu t l.
        induction l as [| l' j_last] using last_ind; simpl in *.
        {
          by exists None; rewrite mem_zip_nseq_r;
            [by rewrite mem_enum | by rewrite size_enum_ord].
        }
        {
          rewrite /schedule_jobs /try_to_schedule_every_job -cats1 foldl_cat /=.
          move: IHl => [x IN].
          eapply replace_first_previous in IN; des;
            first by exists x; apply IN.
          rewrite /set_pair_2nd in IN.
          by exists (Some j_last); apply IN0.
        }
      Qed.

      (* Next, consider a list of jobs l that is sorted by priority and does not have
         duplicates.
         We prove that for any job j in l, if j is not scheduled at time t,
         then every cpu in j's affinity has some job mapped at time t.  *)
      Lemma scheduler_mapping_is_work_conserving :
        forall j cpu t l,
          j \in l ->
          sorted (higher_eq_priority t) l ->
          uniq l ->
          (forall cpu, (cpu, Some j) \notin schedule_jobs l t) ->
          can_execute_on alpha (job_task j) cpu ->
          exists j_other,
            (cpu, Some j_other) \in schedule_jobs l t.
      Proof.
        intros j cpu t l IN SORT UNIQ NOTSCHED CAN.
        
        generalize dependent cpu.
        induction l as [| l' j_last] using last_ind; simpl in *;
          first by rewrite in_nil in IN.
        {
          intros cpu CAN.
          rewrite rcons_uniq in UNIQ; move: UNIQ => /andP [NOTIN UNIQ].
          rewrite /schedule_jobs /try_to_schedule_every_job -cats1 foldl_cat /= in NOTSCHED *.
          set prev := foldl (update_available_cpu  _ _ _ _ _ _) (zip _ _) l' in NOTSCHED *.
          rewrite mem_rcons in_cons in IN.
          move: IN => /orP [/eqP IN | LAST]; subst.
          {
            clear IHl.
            assert (ALL: forall x, x \in prev -> ~~ (should_be_scheduled job_task num_cpus arr_seq
                                                            alpha higher_eq_priority j_last t) x).
            {
              apply replace_first_failed with (f := set_pair_2nd (Some j_last)).
              by intros [cpu' j'] IN; apply NOTSCHED.
            }
            have [x IN] := scheduler_has_cpus cpu t l'; fold prev in IN.
            specialize (ALL (cpu, x) IN).
            simpl in ALL.
            destruct x as [j' |]; last by rewrite CAN in ALL.
            eapply replace_first_previous in IN; des;
              first by exists j'; apply IN.
            by exists j_last; apply IN0.              
          }
          {
            specialize (IHl LAST).
            feed_n 2 IHl;
              [by apply sorted_rcons_prefix in SORT | by done | ].
            feed IHl.
            {
              clear IHl; intros cpu'; specialize (NOTSCHED cpu').
              apply/negP; intro BUG.
              apply replace_first_previous with (f := set_pair_2nd (Some j_last))
                (P := should_be_scheduled job_task num_cpus arr_seq alpha higher_eq_priority j_last t)
                in BUG; des;
                first by rewrite BUG in NOTSCHED.
              move: BUG => /andP [_ /negP HP].
              by apply HP, order_sorted_rcons with (s := l'); try by done.
            }
            move: (IHl cpu CAN) => [j_old IN]; clear IHl LAST.
            by eapply replace_first_previous in IN; des;
              [exists j_old; apply IN | exists j_last; apply IN0].
          }
        }
      Qed.

      (* Next, we prove that the mapping enforces priority. *)
      Lemma scheduler_priority :
        forall j j_hp cpu t,
          backlogged job_cost sched j t ->
          can_execute_on alpha (job_task j) cpu ->
          scheduled_on sched j_hp cpu t ->
          higher_eq_priority t j_hp j.
      Proof.
        have SCHED_ON := scheduler_scheduled_on.
        intros j j_hp cpu t BACK CAN SCHED.
        move: BACK => /andP [PENDING NOTSCHED'].
        assert (NOTSCHED: forall cpu, (cpu, Some j) \notin schedule_pending_jobs t). 
        {
          intros cpu'; rewrite -SCHED_ON.
          by rewrite negb_exists in NOTSCHED'; move: NOTSCHED' => /forallP ALL; apply ALL.
        }
        rewrite SCHED_ON in SCHED.
        clear NOTSCHED' SCHED_ON.

        unfold schedule_pending_jobs, schedule_jobs, schedule_every_pending_job in *.
        set l := sorted_pending_jobs _ _ _ _ _ _ in SCHED NOTSCHED.
        
        have IN: j \in l.
        {
          rewrite mem_sort mem_filter PENDING andTb JobIn_arrived.
          by move: PENDING => /andP [H _].
        }
        have INhp: j_hp \in l by apply scheduler_job_in_mapping in SCHED.
        have SORT : sorted (higher_eq_priority t) l by apply sort_sorted.
        have UNIQ: uniq l by rewrite sort_uniq filter_uniq // JobIn_uniq //.

        induction l as [| l' j_last] using last_ind;
          first by rewrite in_nil in IN.
        {
          rewrite /try_to_schedule_every_job -cats1 foldl_cat /= in SCHED.
          rewrite /try_to_schedule_every_job -cats1 foldl_cat /= in NOTSCHED.
          set prev := foldl (update_available_cpu job_task num_cpus arr_seq alpha higher_eq_priority t) (zip (enum (processor num_cpus)) (nseq num_cpus None)) l' in SCHED NOTSCHED.
          rewrite rcons_uniq in UNIQ; move: UNIQ => /andP [NOTIN UNIQ].
          rewrite 2!mem_rcons 2!in_cons in IN INhp.
          move: IN => /orP [/eqP EQ | IN];
          move: INhp => /orP [/eqP EQhp | INhp].
          {
            subst j_last j_hp.
            by specialize (NOTSCHED cpu); rewrite SCHED in NOTSCHED.
          }
          {
            subst j_last.
            by apply order_sorted_rcons with (s := l').
          }
          {
            subst j_last; clear IHl.
            destruct (replace_first_cases SCHED) as [PREV | [[cpu' y] [EQ [SHOULD IN']]]].
            {
              unfold prev in PREV.
              apply scheduler_job_in_mapping in PREV.
              by rewrite PREV in NOTIN.
            }
            {
              move: EQ; case; intro EQ1; subst cpu'.
              destruct y as [j'|].
              {
                unfold should_be_scheduled in SHOULD.
                move: SHOULD => /andP [CAN' /negP HP].
                unfold prev in IN'.
                apply scheduler_job_in_mapping in IN'.
                by exfalso; apply HP, order_sorted_rcons with (s := l').
              }
              {
                destruct [exists cpu, ((cpu, Some j) \in prev)] eqn:EX.
                {
                  move: EX => /existsP [cpu' IN''].
                  unfold prev in IN''.
                  apply replace_first_previous with (f := set_pair_2nd (Some j_hp)) (P := should_be_scheduled job_task num_cpus arr_seq alpha higher_eq_priority j_hp t) in IN''; des;
                    first by specialize (NOTSCHED cpu'); rewrite IN'' in NOTSCHED.
                  move: IN'' => /andP [_ /negP HP].
                  by exfalso; apply HP, order_sorted_rcons with (s := l').
                }
                {
                  apply negbT in EX; rewrite negb_exists in EX.
                  move: EX => /forallP EX.
                  apply sorted_rcons_prefix in SORT.
                  move: (scheduler_mapping_is_work_conserving j cpu t l' IN SORT UNIQ EX CAN) => [j' BUG].
                  have MEM := pairs_to_function_mem None.
                  apply MEM in BUG; last by apply scheduler_uniq_cpus.
                  have UNIQ' := scheduler_uniq_cpus t l'.
                  apply MEM in IN'; last by apply UNIQ'.
                  by rewrite IN' in BUG.
                }
              }
            }
          }
          {
            apply IHl; try (by done); last first.
            {
              by apply sorted_rcons_prefix in SORT.
            }
            {
              intros cpu0; apply/negP; intro BUG.
              unfold update_available_cpu in NOTSCHED.
              apply replace_first_previous with (f := set_pair_2nd (Some j_last)) (P := should_be_scheduled job_task num_cpus arr_seq alpha higher_eq_priority j_last t) in BUG; des.
              {
                by specialize (NOTSCHED cpu0); rewrite BUG in NOTSCHED.
              }
              {
                move: BUG => /andP [_ /negP HP].
                by apply HP, order_sorted_rcons with (s := l'); try by done.
              }
            }
            {
              destruct (replace_first_cases SCHED) as [| [[cpu' y][EQ [SHOULD IN']]]]; first by done.
              move: EQ; case; intros EQ1 EQ2; subst cpu' j_last.
              by rewrite INhp in NOTIN.
            }
          }
        }
      Qed.

    End HelperLemmas.

    (* Now, we prove the important properties about the implementation. *)
    
    (* Jobs do not execute before they arrive, ...*)
    Theorem scheduler_jobs_must_arrive_to_execute:
      jobs_must_arrive_to_execute sched.
    Proof.
      unfold jobs_must_arrive_to_execute.
      intros j t SCHED.
      move: SCHED => /existsP [cpu /eqP SCHED].
      unfold sched, scheduler, schedule_prefix in SCHED.
      destruct t.
      {
        rewrite /update_schedule eq_refl in SCHED.
        apply pairs_to_function_neq_default in SCHED; last by done.
        unfold schedule_every_pending_job in SCHED.
        apply scheduler_job_in_mapping in SCHED.
        rewrite mem_sort mem_filter in SCHED.
        move: SCHED => /andP [_ ARR].
        by apply JobIn_arrived in ARR.
      }
      {
        unfold update_schedule at 1 in SCHED; rewrite eq_refl /= in SCHED.
        apply pairs_to_function_neq_default in SCHED; last by done.
        unfold schedule_every_pending_job in SCHED.
        apply scheduler_job_in_mapping in SCHED.
        rewrite mem_sort mem_filter in SCHED.
        move: SCHED => /andP [_ ARR].
        by apply JobIn_arrived in ARR.
      }
    Qed.

    (* ..., jobs are sequential, ... *)
    Theorem scheduler_sequential_jobs: sequential_jobs sched.
    Proof.
      intros j t cpu1 cpu2 SCHED1 SCHED2.
      by apply scheduler_has_no_duplicate_jobs with (j := j) (t := t);
        rewrite -scheduler_scheduled_on; apply/eqP.
    Qed.
               
    (* ... and jobs do not execute after completion. *)
    Theorem scheduler_completed_jobs_dont_execute:
      completed_jobs_dont_execute job_cost sched.
    Proof.
      have SEQ := scheduler_sequential_jobs.
      rename H_job_cost_positive into GT0.
      unfold completed_jobs_dont_execute, service.
      intros j t.
      induction t; first by rewrite big_geq.
      {
        rewrite big_nat_recr // /=.
        rewrite leq_eqVlt in IHt; move: IHt => /orP [/eqP EQ | LESS]; last first.
        {
          destruct (job_cost j); first by rewrite ltn0 in LESS.
          rewrite -addn1; rewrite ltnS in LESS.
          by apply leq_add; last by apply service_at_most_one, SEQ. 
        }
        rewrite EQ -{2}[job_cost j]addn0; apply leq_add; first by done.
        destruct t.
        {
          rewrite big_geq // in EQ.
          specialize (GT0 j); unfold job_cost_positive in *.
          by rewrite -EQ ltn0 in GT0.
        }
        {
          unfold service_at; rewrite big_mkcond.
          apply leq_trans with (n := \sum_(cpu < num_cpus) 0);
            last by rewrite big_const_ord iter_addn mul0n addn0.
          apply leq_sum; intros cpu _; desf.
          move: Heq => /eqP SCHED.
          unfold scheduler, schedule_prefix in SCHED.
          unfold sched, scheduler, schedule_prefix, update_schedule at 1 in SCHED.
          rewrite eq_refl in SCHED.
          apply pairs_to_function_neq_default in SCHED; last by done.
          unfold schedule_every_pending_job in SCHED.
          apply scheduler_job_in_mapping in SCHED.
          rewrite mem_sort mem_filter in SCHED.
          move: SCHED => /andP [/andP [_ /negP NOTCOMP] _].
          exfalso; apply NOTCOMP; clear NOTCOMP.
          unfold completed; apply/eqP.
          unfold service; rewrite -EQ.
          rewrite big_nat_cond [\sum_(_ <= _ < _ | true)_]big_nat_cond.
          apply eq_bigr; move => i /andP [/andP [_ LT] _].
          apply eq_bigl; red; ins.
          unfold scheduled_on; f_equal.
          fold (schedule_prefix job_cost job_task num_cpus arr_seq alpha higher_eq_priority).
          by rewrite scheduler_same_prefix.
        }
      }
    Qed.

    (* In addition, the scheduler is APA work conserving, ... *)
    Theorem scheduler_apa_work_conserving:
      apa_work_conserving job_cost job_task sched alpha.
    Proof.
      intros j t BACK cpu CAN.
      set l := (sorted_pending_jobs job_cost num_cpus arr_seq higher_eq_priority sched t).
      have SORT : sorted (higher_eq_priority t) l  by apply sort_sorted.
      have UNIQ: uniq l by rewrite sort_uniq filter_uniq // JobIn_uniq //.
      move: BACK => /andP [PENDING NOTSCHED].
      have IN: j \in l.
      {
        rewrite mem_sort mem_filter PENDING andTb JobIn_arrived.
        by move: PENDING => /andP [H _].
      }
      have WORK := scheduler_mapping_is_work_conserving j cpu t l IN SORT UNIQ.
      exploit WORK; try by done.
      {
        rewrite negb_exists in NOTSCHED; move: NOTSCHED => /forallP NOTSCHED.
        by intros cpu0; specialize (NOTSCHED cpu0); rewrite -scheduler_scheduled_on.
      }
      by move => [j_other IN']; exists j_other; rewrite scheduler_scheduled_on.
    Qed.  

    (* ..., respects affinities, ... *)
    Theorem scheduler_respects_affinity:
      respects_affinity job_task sched alpha.
    Proof.
      unfold respects_affinity; intros j cpu t SCHED.
      apply scheduler_mapping_respects_affinity with (t := t).
      by rewrite -scheduler_scheduled_on.
    Qed.
    
    (* ... and enforces the JLDP policy under weak APA scheduling. *)
    Theorem scheduler_enforces_policy :
      enforces_JLDP_policy_under_weak_APA job_cost job_task sched alpha higher_eq_priority.
    Proof.
      unfold enforces_JLDP_policy_under_weak_APA.
      intros j j_hp cpu t BACK SCHED ALPHA.
      rewrite scheduler_scheduled_on in SCHED.
      apply scheduler_priority with (cpu := cpu); try by done.
      by rewrite scheduler_scheduled_on.
    Qed.

  End Proofs.
    
End ConcreteScheduler.