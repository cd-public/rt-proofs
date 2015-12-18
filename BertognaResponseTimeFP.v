Require Import Vbase ScheduleDefs BertognaResponseTimeDefs divround helper
               ssreflect ssrbool eqtype ssrnat seq fintype bigop div path tuple.

Module ResponseTimeIterationFP.

  Import Schedule ResponseTimeAnalysis.

  Section Analysis.
    
    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> nat.
    Variable task_period: sporadic_task -> nat.
    Variable task_deadline: sporadic_task -> nat.
    
    Let task_with_response_time := (sporadic_task * nat)%type.
    
    Context {Job: eqType}.
    Variable job_cost: Job -> nat.
    Variable job_deadline: Job -> nat.
    Variable job_task: Job -> sporadic_task.

    Variable num_cpus: nat.
    Variable higher_eq_priority: fp_policy sporadic_task.
    Hypothesis H_valid_policy: valid_fp_policy higher_eq_priority.

    (* Next we define the fixed-point iteration for computing
       Bertogna's response-time bound for any task in ts. *)
    
    (* First, given a sequence of pairs R_prev = [..., (tsk_hp, R_hp)] of
       response-time bounds for the higher-priority tasks, we compute
       the response-time bound of tsk using the following iteration:

       R_tsk <- f^step (R_tsk),
         where f is the response-time recurrence,
         step is the number of iterations,
         and f^0 = task_cost tsk. *)
    Definition per_task_rta (tsk: sporadic_task)
                      (R_prev: seq task_with_response_time) (step: nat) :=
      iter step
        (fun t => task_cost tsk +
                  div_floor
                    (total_interference_bound_fp task_cost task_period tsk
                                                R_prev t higher_eq_priority)
                    num_cpus)
        (task_cost tsk).

    (* To ensure that the iteration converges, we will apply per_task_rta
       a "sufficient" number of times: task_deadline tsk + 1.
       Note that (deadline + 1) is a pessimistic bound on the number of
       steps, but we don't care about precise runtime complexity here. *)
    Definition max_steps (tsk: sporadic_task) := task_deadline tsk + 1.
    
    (* Next we compute the response-time bounds for the entire task set.
       Since high-priority tasks may not be schedulable, we allow the
       computation to fail.
       Thus, given the response-time bound of previous tasks, we either
       (a) append the response-time bound (tsk, R) of the current task
           to the list of pairs, or,
       (b) return None if the response-time analysis failed. *)
    Definition R_list_helper :=
      fun hp_pairs tsk =>
               if hp_pairs is Some rt_bounds then
                 let R := per_task_rta tsk rt_bounds (max_steps tsk) in
                   if R <= task_deadline tsk then
                     Some (rcons rt_bounds (tsk, R))
                   else None
               else None.

    (* To return the complete list of response-time bounds for any task set,
       we just apply foldl (reduce) using the function above. *)
    Definition R_list (ts: taskset_of sporadic_task) : option (seq task_with_response_time) :=
      foldl R_list_helper (Some [::]) ts.

    (* The schedulability test simply checks if we got a list of
       response-time bounds (i.e., if the computation did not fail). *)
    Definition fp_schedulable (ts: taskset_of sporadic_task) :=
      R_list ts != None.
    
    Section AuxiliaryLemmas.

      (* In this section, we prove several helper lemmas about the
         list of response-time bounds, such as:
         (1) Equality among tasks in R_list and in the task set.
         (2) If (tsk, R) \in R_list, then R <= task_deadline tsk.
         (3) If (tsk, R) \in R_list, then R >= task_cost tsk.
         (4) If per_task_rta returns a bound <= deadline, then the
             iteration reached a fixed-point. *)

      Lemma R_list_rcons_prefix :
        forall ts' hp_bounds tsk1 tsk2 R,
          R_list (rcons ts' tsk1) = Some (rcons hp_bounds (tsk2, R)) ->
            R_list ts' = Some hp_bounds.
      Proof.
        intros ts hp_bounds tsk1 tsk2 R SOME.
        rewrite -cats1 in SOME.
        unfold R_list in *.
        rewrite foldl_cat in SOME.
        simpl in SOME.
        unfold R_list_helper in SOME.
        desf; rewrite Heq; rename H0 into EQ.
        move: EQ => /eqP EQ.
        rewrite eqseq_rcons in EQ.
        move: EQ => /andP [/eqP EQ _].
        by f_equal.
      Qed. 

      Lemma R_list_rcons_task :
        forall ts' hp_bounds tsk1 tsk2 R,
          R_list (rcons ts' tsk1) = Some (rcons hp_bounds (tsk2, R)) ->
            tsk1 = tsk2.
      Proof.
        intros ts hp_bounds tsk1 tsk2 R SOME.
        rewrite -cats1 in SOME.
        unfold R_list in *.
        rewrite foldl_cat in SOME.
        simpl in SOME.
        unfold R_list_helper in SOME.
        desf; rename H0 into EQ.
        move: EQ => /eqP EQ.
        rewrite eqseq_rcons in EQ.
        move: EQ => /andP [_ /eqP EQ].
        by inversion EQ.
      Qed. 

      Lemma R_list_rcons_response_time :
        forall ts' hp_bounds tsk R,
          R_list (rcons ts' tsk) = Some (rcons hp_bounds (tsk, R)) ->
            R = per_task_rta tsk hp_bounds (max_steps tsk). 
      Proof.
        intros ts hp_bounds tsk R SOME.
        rewrite -cats1 in SOME.
        unfold R_list in SOME.
        rewrite foldl_cat in SOME.
        simpl in SOME.
        unfold R_list_helper in SOME.
        desf; rename H0 into EQ; move: EQ => /eqP EQ.
        rewrite eqseq_rcons in EQ; move: EQ => /andP [/eqP EQ1 /eqP EQ2].
        by inversion EQ2; rewrite EQ1.
      Qed.

      Lemma R_list_le_deadline :
        forall ts' rt_bounds tsk R,
          R_list ts' = Some rt_bounds ->
          (tsk, R) \in rt_bounds ->
          R <= task_deadline tsk.
      Proof.
        intros ts; induction ts as [| ts' tsk_lst] using last_ind.
        {
          intros rt_bounds tsk R SOME IN.
          by inversion SOME; subst; rewrite in_nil in IN.
        }
        {
          intros rt_bounds tsk_i R SOME IN.
          destruct (lastP rt_bounds) as [|rt_bounds (tsk_lst', R_lst)];
            first by rewrite in_nil in IN.
          rewrite mem_rcons in_cons in IN; move: IN => /orP IN.
          destruct IN as [LAST | FRONT].
          {
            move: LAST => /eqP LAST.
            rewrite -cats1 in SOME.
            unfold R_list in *.
            rewrite foldl_cat in SOME.
            simpl in SOME.
            unfold R_list_helper in SOME.
            desf; rename H0 into EQ.
            move: EQ => /eqP EQ.
            rewrite eqseq_rcons in EQ.
            move: EQ => /andP [_ /eqP EQ].
            inversion EQ; subst.
            by apply Heq0.
          }
          {
            apply IHts with (rt_bounds := rt_bounds); last by ins.
            by apply R_list_rcons_prefix in SOME.
          }
        }
      Qed.

      Lemma R_list_ge_cost :
        forall ts' rt_bounds tsk R,
          R_list ts' = Some rt_bounds ->
          (tsk, R) \in rt_bounds ->
          R >= task_cost tsk.
      Proof.
        intros ts; induction ts as [| ts' tsk_lst] using last_ind.
        {
          intros rt_bounds tsk R SOME IN.
          by inversion SOME; subst; rewrite in_nil in IN.
        }
        {
          intros rt_bounds tsk_i R SOME IN.
          destruct (lastP rt_bounds) as [|rt_bounds (tsk_lst', R_lst)];
            first by rewrite in_nil in IN.
          rewrite mem_rcons in_cons in IN; move: IN => /orP IN.
          destruct IN as [LAST | FRONT].
          {
            move: LAST => /eqP LAST.
            rewrite -cats1 in SOME.
            unfold R_list in *.
            rewrite foldl_cat in SOME.
            simpl in SOME.
            unfold R_list_helper in SOME.
            desf; rename H0 into EQ.
            move: EQ => /eqP EQ.
            rewrite eqseq_rcons in EQ.
            move: EQ => /andP [_ /eqP EQ].
            inversion EQ; subst.
            by destruct (max_steps tsk_lst');
              [by apply leqnn | by apply leq_addr].
          }
          {
            apply IHts with (rt_bounds := rt_bounds); last by ins.
            by apply R_list_rcons_prefix in SOME.
          }
        }
      Qed.

      Lemma R_list_non_empty :
        forall ts' rt_bounds tsk,
          R_list ts' = Some rt_bounds ->
          (tsk \in ts' <->
            exists R,
              (tsk, R) \in rt_bounds).
      Proof.
        intros ts; induction ts as [| ts' tsk_lst] using last_ind.
        {
          intros rt_bounds tsk SOME.
          inversion SOME; rewrite in_nil; split; first by ins.
          by intro EX; des; rewrite in_nil in EX.
        }
        {
          intros rt_bounds tsk_i SOME.
          destruct (lastP rt_bounds) as [|rt_bounds (tsk_lst', R_lst)].
          {
            split; last first; intro EX; des; first by rewrite in_nil in EX.
            unfold R_list in *.
            rewrite -cats1 foldl_cat in SOME.
            simpl in SOME.
            unfold R_list_helper in *; desf; rename H0 into EQ.
            destruct l; first by ins.
            by rewrite rcons_cons in EQ; inversion EQ.
          }
          split.
          {
            intros IN; rewrite mem_rcons in_cons in IN; move: IN => /orP IN.
            destruct IN as [LAST | FRONT].
            {
              move: LAST => /eqP LAST; subst tsk_i.
              generalize SOME; apply R_list_rcons_task in SOME; subst tsk_lst'; intro SOME.
              exists R_lst.
              by rewrite mem_rcons in_cons; apply/orP; left.
            }
            {
              apply R_list_rcons_prefix in SOME.
              exploit (IHts rt_bounds tsk_i); [by ins | intro EX].
              apply EX in FRONT; des.
              by exists R; rewrite mem_rcons in_cons; apply/orP; right.
            }
          }
          {
            intro IN; des.
            rewrite mem_rcons in_cons in IN; move: IN => /orP IN.
            destruct IN as [LAST | FRONT].
            {
              move: LAST => /eqP LAST.
              inversion LAST; subst tsk_i R; clear LAST.
              apply R_list_rcons_task in SOME; subst.
              by rewrite mem_rcons in_cons; apply/orP; left.
            }
            {
              rewrite mem_rcons in_cons; apply/orP; right.
              exploit (IHts rt_bounds tsk_i);
                [by apply R_list_rcons_prefix in SOME | intro EX].
              by apply EX; exists R.
            }
          }
        }
      Qed.

      (*  To prove convergence of R, we first show convergence of rt_rec. *)      Lemma per_task_rta_converges:
        forall ts' tsk rt_bounds,
          valid_sporadic_taskset task_cost task_period task_deadline ts' ->
          R_list ts' = Some rt_bounds ->
          per_task_rta tsk rt_bounds (max_steps tsk) <= task_deadline tsk ->
            per_task_rta tsk rt_bounds (max_steps tsk) =
              per_task_rta tsk rt_bounds (max_steps tsk).+1.
      Proof.
        unfold valid_sporadic_taskset, is_valid_sporadic_task in *.
        
        (* To simplify, let's call the function f.*)
        intros ts' tsk rt_bounds VALID SOME LE;
          set (f := per_task_rta tsk rt_bounds); fold f in LE.

        (* First prove that f is monotonic.*)
        assert (MON: forall x1 x2, x1 <= x2 -> f x1 <= f x2).
        {
          intros x1 x2 LEx; unfold f, per_task_rta.
          apply fun_mon_iter_mon; [by ins | by ins; apply leq_addr |].
          clear LEx x1 x2; intros x1 x2 LEx.
          
          unfold div_floor, total_interference_bound_fp.
          rewrite big_seq_cond [\sum_(i <- _ | let '(tsk_other, _) := i in
                                   _ && (tsk_other != tsk))_]big_seq_cond.
          rewrite leq_add2l leq_div2r // leq_sum //.

          intros i; destruct (i \in rt_bounds) eqn:HP;
            last by rewrite andFb.
          destruct i as [i R]; intros _.
          have GE_COST := (R_list_ge_cost ts' rt_bounds i R).
          have INts := (R_list_non_empty ts' rt_bounds i SOME).
          destruct INts as [_ EX]; exploit EX; [by exists R | intro IN].
          unfold interference_bound; simpl.
          rewrite leq_min; apply/andP; split.
          {
            apply leq_trans with (n := W task_cost task_period i R x1); 
              first by apply geq_minl.            
            specialize (VALID i IN); des.
            by apply W_monotonic; try (by ins);
              [by apply GE_COST | by apply leqnn].
          }
          {
            apply leq_trans with (n := x1 - task_cost tsk + 1);
              first by apply geq_minr.
            by rewrite leq_add2r leq_sub2r //.
          }
        }

        (* Either f converges by the deadline or not. *)
        unfold max_steps in *; rewrite -> addn1 in *.
        destruct ([exists k in 'I_(task_deadline tsk).+1,
                     f k == f k.+1]) eqn:EX.
        {
          move: EX => /exists_inP EX; destruct EX as [k _ ITERk].
          move: ITERk => /eqP ITERk.
          by apply iter_fix with (k := k);
            [by ins | by apply ltnW, ltn_ord].
        }
        apply negbT in EX; rewrite negb_exists_in in EX.
        move: EX => /forall_inP EX.
        assert (GROWS: forall k: 'I_(task_deadline tsk).+1,
                         f k < f k.+1).
        {
          intros k; rewrite ltn_neqAle; apply/andP; split; first by apply EX.
          apply MON, leqnSn.
        }

        (* If it doesn't converge, then it becomes larger than the deadline.
           But initialy we assumed otherwise. Contradiction! *)
        assert (BY1: f (task_deadline tsk).+1 > task_deadline tsk).
        {
          clear MON LE EX.
          induction (task_deadline tsk).+1; first by ins.
          apply leq_ltn_trans with (n := f n);
            last by apply (GROWS (Ordinal (ltnSn n))).
          apply IHn; intros k.
          by apply (GROWS (widen_ord (leqnSn n) k)).
        }
        by apply leq_ltn_trans with (m := f (task_deadline tsk).+1) in BY1;
          [by rewrite ltnn in BY1 | by ins].
      Qed.

      Lemma per_task_rta_fold :
        forall tsk rt_bounds,
          task_cost tsk +
           div_floor (total_interference_bound_fp task_cost task_period tsk rt_bounds
                     (per_task_rta tsk rt_bounds (max_steps tsk)) higher_eq_priority) num_cpus
          = per_task_rta tsk rt_bounds (max_steps tsk).+1.
      Proof.
          by ins.
      Qed.

      Lemma R_list_unzip1 :
        forall ts' tsk hp_bounds R,
          transitive higher_eq_priority ->
          uniq (rcons ts' tsk) ->
          sorted higher_eq_priority (rcons ts' tsk) ->
          R_list (rcons ts' tsk) = Some (rcons hp_bounds (tsk, R)) ->
            [seq tsk_hp <- rcons ts' tsk | is_interfering_task_fp higher_eq_priority tsk tsk_hp] =
            unzip1 hp_bounds.
      Proof.
        intros ts tsk hp_bounds R TRANS.
        revert tsk hp_bounds R.
        induction ts as [| ts' tsk_lst] using last_ind.
        {
          intros tsk hp_bounds R _ _ SOME; simpl in *.
          unfold is_interfering_task_fp.
          rewrite eq_refl andbF.
          destruct hp_bounds; first by ins.
          unfold R_list in SOME; inversion SOME; desf.
          by destruct hp_bounds.
        }
        {
          intros tsk hp_bounds R UNIQ SORTED SOME.
          destruct (lastP hp_bounds) as [| hp_bounds (tsk_lst', R_lst)].
          {
            apply R_list_rcons_prefix in SOME.
            unfold R_list in SOME.
            rewrite -cats1 foldl_cat in SOME.
            unfold R_list_helper in SOME.
            inversion SOME; desf.
            by destruct l.
          }
          generalize SOME; apply R_list_rcons_prefix, R_list_rcons_task in SOME; subst tsk_lst'; intro SOME.
          specialize (IHts tsk_lst hp_bounds R_lst).
          rewrite filter_rcons in IHts.
          unfold is_interfering_task_fp in IHts.
          rewrite eq_refl andbF in IHts.
          assert (NOTHP: is_interfering_task_fp higher_eq_priority tsk tsk = false).
          {
            by unfold is_interfering_task_fp; rewrite eq_refl andbF.
          } rewrite filter_rcons NOTHP; clear NOTHP.
          assert (HP: is_interfering_task_fp higher_eq_priority tsk tsk_lst).
          {
            unfold is_interfering_task_fp; apply/andP; split.
            {
              apply order_sorted_rcons with (x := tsk_lst) in SORTED; try (by ins).
              by rewrite mem_rcons in_cons; apply/orP; left.
            }
            {
              rewrite 2!rcons_uniq mem_rcons in_cons negb_or in UNIQ.
              move : UNIQ => /andP [/andP [UNIQ _] _].
              by rewrite eq_sym in UNIQ.
            }
          } rewrite filter_rcons HP; clear HP.
          unfold unzip1; rewrite map_rcons /=; f_equal.
          assert (SHIFT: [seq tsk_hp <- ts' | is_interfering_task_fp higher_eq_priority tsk tsk_hp] = [seq tsk_hp <- ts'
      | is_interfering_task_fp higher_eq_priority tsk_lst tsk_hp]).
          {
            apply eq_in_filter; red.
            unfold is_interfering_task_fp; intros x INx.
            rewrite 2!rcons_uniq mem_rcons in_cons negb_or in UNIQ.
            move: UNIQ => /andP [/andP [NEQ NOTIN] /andP [NOTIN' UNIQ]].
            destruct (x == tsk) eqn:EQtsk.
            {
              move: EQtsk => /eqP EQtsk; subst.
              by rewrite INx in NOTIN.
            }
            destruct (x == tsk_lst) eqn:EQlst.
            {
              move: EQlst => /eqP EQlst; subst.
              by rewrite INx in NOTIN'.
            }
            rewrite 2!andbT.
            generalize SORTED; intro SORTED'.
            have bla := order_sorted_rcons.
            apply order_sorted_rcons with (x0 := x) in SORTED; try (by ins);
              last by rewrite mem_rcons in_cons; apply/orP; right.
            rewrite SORTED.
            apply sorted_rcons_prefix in SORTED'.
            by apply order_sorted_rcons with (x0 := x) in SORTED'.
          } rewrite SHIFT; clear SHIFT.
          apply IHts.
            by rewrite rcons_uniq in UNIQ; move: UNIQ => /andP [_ UNIQ].
            by apply sorted_rcons_prefix in SORTED.
            by apply R_list_rcons_prefix in SOME.
        }
      Qed.
      
    End AuxiliaryLemmas.
    
    Section Proof.

      (* Consider a task set ts. *)
      Variable ts: taskset_of sporadic_task.
      
      (* Assume that higher_eq_priority is a total order.
         Actually, it just needs to be total over the task set,
         but to weaken the assumption, I have to re-prove many lemmas
         about ordering in ssreflect. This can be done later. *)
      Hypothesis H_reflexive: reflexive higher_eq_priority.
      Hypothesis H_transitive: transitive higher_eq_priority.
      Hypothesis H_unique_priorities: antisymmetric higher_eq_priority.
      Hypothesis H_total: total higher_eq_priority.

      (* Assume the task set has no duplicates, ... *)
      Hypothesis H_ts_is_a_set: uniq ts.

      (* ...all tasks have valid parameters, ... *)
      Hypothesis H_valid_task_parameters:
        valid_sporadic_taskset task_cost task_period task_deadline ts.

      (* ...restricted deadlines, ...*)
      Hypothesis H_restricted_deadlines:
        forall tsk, tsk \in ts -> task_deadline tsk <= task_period tsk.

      (* ...and tasks are ordered by increasing priorities. *)
      Hypothesis H_sorted_ts: sorted higher_eq_priority ts.

      (* Next, consider any arrival sequence such that...*)
      Context {arr_seq: arrival_sequence Job}.

     (* ...all jobs come from task set ts, ...*)
      Hypothesis H_all_jobs_from_taskset:
        forall (j: JobIn arr_seq), job_task j \in ts.
      
      (* ...they have valid parameters,...*)
      Hypothesis H_valid_job_parameters:
        forall (j: JobIn arr_seq),
          valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j.
      
      (* ... and satisfy the sporadic task model.*)
      Hypothesis H_sporadic_tasks:
        sporadic_task_model task_period arr_seq job_task.
      
      (* Then, consider any platform with at least one CPU and unit
         unit execution rate, where...*)
      Variable rate: Job -> processor num_cpus -> nat.
      Variable sched: schedule num_cpus arr_seq.
      Hypothesis H_at_least_one_cpu :
        num_cpus > 0.
      Hypothesis H_rate_equals_one :
        forall j cpu, rate j cpu = 1.

      (* ...jobs only execute after they arrived and no longer
         than their execution costs,... *)
      Hypothesis H_jobs_must_arrive_to_execute:
        jobs_must_arrive_to_execute sched.
      Hypothesis H_completed_jobs_dont_execute:
        completed_jobs_dont_execute job_cost rate sched.

      (* ...and do not execute in parallel. *)
      Hypothesis H_no_parallelism:
        jobs_dont_execute_in_parallel sched.

      (* Assume the platform satisfies the global scheduling invariant. *)
      Hypothesis H_global_scheduling_invariant:
        FP_scheduling_invariant_holds job_cost job_task num_cpus rate sched ts higher_eq_priority.

      Definition no_deadline_missed_by_task (tsk: sporadic_task) :=
        task_misses_no_deadline job_cost job_deadline job_task rate sched tsk.
      Definition no_deadline_missed_by_job :=
        job_misses_no_deadline job_cost job_deadline rate sched.

      Section HelperLemma.
        
        (* The following lemma states that the response-time bounds
           computed using R_list are valid. *)
        Lemma R_list_has_response_time_bounds :
          forall rt_bounds tsk R,
            R_list ts = Some rt_bounds ->
            (tsk, R) \in rt_bounds ->
            forall j : JobIn arr_seq,
              job_task j = tsk ->
              completed job_cost rate sched j (job_arrival j + R).
        Proof.
          rename H_valid_job_parameters into JOBPARAMS,
                 H_valid_task_parameters into TASKPARAMS,
                 H_restricted_deadlines into RESTR,
                 H_completed_jobs_dont_execute into COMP,
                 H_jobs_must_arrive_to_execute into MUSTARRIVE,
                 H_global_scheduling_invariant into INVARIANT,
                 H_sorted_ts into SORT,
                 H_transitive into TRANS,
                 H_unique_priorities into UNIQ,
                 H_total into TOTAL,
                 H_all_jobs_from_taskset into ALLJOBS,
                 H_ts_is_a_set into SET.
          clear ALLJOBS.
        
          unfold fp_schedulable, R_list in *.
          induction ts as [| ts' tsk_i IH] using last_ind.
          {
            intros rt_bounds tsk R SOME IN.
            by inversion SOME; subst; rewrite in_nil in IN.
          }
          {
           intros rt_bounds tsk R SOME IN j JOBj.
             destruct (lastP rt_bounds) as [| hp_bounds (tsk_lst, R_lst)];
              first by rewrite in_nil in IN.
            rewrite mem_rcons in_cons in IN; move: IN => /orP IN.
            destruct IN as [LAST | BEGINNING]; last first.
            {
              apply IH with (rt_bounds := hp_bounds) (tsk := tsk); try (by ins).
              by rewrite rcons_uniq in SET; move: SET => /andP [_ SET].
              by ins; red; ins; apply TASKPARAMS; rewrite mem_rcons in_cons; apply/orP; right.
              by ins; apply RESTR; rewrite mem_rcons in_cons; apply/orP; right.
              by apply sorted_rcons_prefix in SORT.
              {
                intros tsk0 j0 t IN0 JOB0 BACK0.
                exploit (INVARIANT tsk0 j0 t); try (by ins);
                  [by rewrite mem_rcons in_cons; apply/orP; right | intro INV].
                rewrite -cats1 count_cat /= in INV.
                unfold is_interfering_task_fp in INV.
                generalize SOME; apply R_list_rcons_task in SOME; subst tsk_i; intro SOME.
                assert (HP: higher_eq_priority tsk_lst tsk0 = false).
                {
                  apply order_sorted_rcons with (x := tsk0) in SORT; [|by ins | by ins].
                  apply negbTE; apply/negP; unfold not; intro BUG.
                  exploit UNIQ; [by apply/andP; split; [by apply SORT | by ins] | intro EQ].
                  by rewrite rcons_uniq -EQ IN0 in SET.
                }              
                by rewrite HP 2!andFb 2!addn0 in INV.
              }
              by apply R_list_rcons_prefix in SOME.
            }
            {
              move: LAST => /eqP LAST.
              inversion LAST as [[EQ1 EQ2]].
              rewrite -> EQ1 in *; rewrite -> EQ2 in *; clear EQ1 EQ2 LAST.
              generalize SOME; apply R_list_rcons_task in SOME; subst tsk_i; intro SOME.
              generalize SOME; apply R_list_rcons_prefix in SOME; intro SOME'.
              have BOUND := bertogna_cirinei_response_time_bound_fp.
              unfold is_response_time_bound_of_task in BOUND.
              apply BOUND with (task_cost := task_cost) (task_period := task_period) (task_deadline := task_deadline) (job_deadline := job_deadline) (job_task := job_task) (tsk := tsk_lst)
                               (ts := rcons ts' tsk_lst) (hp_bounds := hp_bounds)
                               (higher_eq_priority := higher_eq_priority); clear BOUND; try (by ins).
              by rewrite mem_rcons in_cons eq_refl orTb.
              by apply R_list_unzip1 with (R := R_lst).
              {
                intros hp_tsk R0 HP j0 JOB0.
                apply IH with (rt_bounds := hp_bounds) (tsk := hp_tsk); try (by ins).
                by rewrite rcons_uniq in SET; move: SET => /andP [_ SET].
                by red; ins; apply TASKPARAMS; rewrite mem_rcons in_cons; apply/orP; right.
                by ins; apply RESTR; rewrite mem_rcons in_cons; apply/orP; right.
                by apply sorted_rcons_prefix in SORT.
                {
                  intros tsk0 j1 t IN0 JOB1 BACK0.
                  exploit (INVARIANT tsk0 j1 t); try (by ins);
                    [by rewrite mem_rcons in_cons; apply/orP; right | intro INV].
                  rewrite -cats1 count_cat /= addn0 in INV.
                  unfold is_interfering_task_fp in INV.
                  assert (NOINTERF: higher_eq_priority tsk_lst tsk0 = false).
                  {
                    apply order_sorted_rcons with (x := tsk0) in SORT; [|by ins | by ins].
                    apply negbTE; apply/negP; unfold not; intro BUG.
                    exploit UNIQ; [by apply/andP; split; [by apply BUG | by ins] | intro EQ].
                    by rewrite rcons_uniq EQ IN0 in SET.
                  }
                  by rewrite NOINTERF 2!andFb addn0 in INV.
                }
              }
              by ins; apply R_list_ge_cost with (ts' := ts') (rt_bounds := hp_bounds).
              by ins; apply R_list_le_deadline with (ts' := ts') (rt_bounds := hp_bounds).
              {
                rewrite [R_lst](R_list_rcons_response_time ts' hp_bounds tsk_lst); last by ins.
                rewrite per_task_rta_fold.
                apply per_task_rta_converges with (ts' := ts'); try (by ins).
                {
                  red; ins; apply TASKPARAMS.
                  by rewrite mem_rcons in_cons; apply/orP; right.
                }
                apply R_list_le_deadline with (ts' := rcons ts' tsk_lst)
                                            (rt_bounds := rcons hp_bounds (tsk_lst, R_lst));
                  first by apply SOME'.
                rewrite mem_rcons in_cons; apply/orP; left; apply/eqP.
                f_equal; symmetry.
                by apply R_list_rcons_response_time with (ts' := ts'). 
              }
            }
          }
        Qed.

      End HelperLemma.
      
      (* If the schedulability test suceeds, ...*)
      Hypothesis H_test_succeeds: fp_schedulable ts.
      
      (*..., then no task misses its deadline,... *)
      Theorem taskset_schedulable_by_fp_rta :
        forall tsk, tsk \in ts -> no_deadline_missed_by_task tsk.
      Proof.
        unfold no_deadline_missed_by_task, task_misses_no_deadline,
               job_misses_no_deadline, completed,
               fp_schedulable,
               valid_sporadic_job in *.
        rename H_valid_job_parameters into JOBPARAMS,
               H_valid_task_parameters into TASKPARAMS,
               H_restricted_deadlines into RESTR,
               H_completed_jobs_dont_execute into COMP,
               H_jobs_must_arrive_to_execute into MUSTARRIVE,
               H_global_scheduling_invariant into INVARIANT,
               H_sorted_ts into SORT,
               H_transitive into TRANS,
               H_unique_priorities into UNIQ,
               H_total into TOTAL,
               H_all_jobs_from_taskset into ALLJOBS,
               H_test_succeeds into TEST.

        move => tsk INtsk j /eqP JOBtsk.
        have RLIST := (R_list_has_response_time_bounds).
        have NONEMPTY := (R_list_non_empty ts).
        have DL := (R_list_le_deadline ts).

        destruct (R_list ts) as [rt_bounds |]; last by ins.
        exploit (NONEMPTY rt_bounds tsk); [by ins | intros [EX _]; specialize (EX INtsk); des].
        exploit (RLIST rt_bounds tsk R); [by ins | by ins | by apply JOBtsk | intro COMPLETED].
        exploit (DL rt_bounds tsk R); [by ins | by ins | clear DL; intro DL].
        
        rewrite eqn_leq; apply/andP; split; first by apply service_interval_le_cost.
        apply leq_trans with (n := service rate sched j (job_arrival j + R)); last first.
        {
          unfold valid_sporadic_taskset, is_valid_sporadic_task in *.
          apply service_monotonic; rewrite leq_add2l.
          specialize (JOBPARAMS j); des; rewrite JOBPARAMS1.
          by rewrite JOBtsk.
        }
        rewrite leq_eqVlt; apply/orP; left; rewrite eq_sym.
        by apply COMPLETED.
      Qed.

      (* ..., and the schedulability test yields safe response-time
         bounds for each task. *)
      Theorem fp_schedulability_test_yields_response_time_bounds :
        forall tsk,
          tsk \in ts ->
          exists R,
            R <= task_deadline tsk /\
            forall (j: JobIn arr_seq),
              job_task j = tsk ->
              completed job_cost rate sched j (job_arrival j + R).
      Proof.
        intros tsk IN.
        unfold fp_schedulable in *.
        have TASKS := R_list_non_empty ts.
        have BOUNDS := (R_list_has_response_time_bounds).
        have DL := (R_list_le_deadline ts).
        destruct (R_list ts) as [rt_bounds |]; last by ins.
        exploit (TASKS rt_bounds tsk); [by ins | clear TASKS; intro EX].
        destruct EX as [EX _]; specialize (EX IN); des.
        exists R; split.
          by apply DL with (rt_bounds0 := rt_bounds).
          by ins; apply (BOUNDS rt_bounds tsk).
      Qed.

      (* For completeness, since all jobs of the arrival sequence
         are spawned by the task set, we conclude that no job misses
         its deadline. *)
      Theorem jobs_schedulable_by_fp_rta :
        forall (j: JobIn arr_seq), no_deadline_missed_by_job j.
      Proof.
        intros j.
        have SCHED := taskset_schedulable_by_fp_rta.
        unfold no_deadline_missed_by_task, task_misses_no_deadline in *.
        apply SCHED with (tsk := job_task j); last by rewrite eq_refl.
        by apply H_all_jobs_from_taskset.
      Qed.
      
    End Proof.

  End Analysis.

End ResponseTimeIterationFP.