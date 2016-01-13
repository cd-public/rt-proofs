Require Import Vbase schedule bertogna_fp_theory util_divround util_lemmas
        ssreflect ssrbool eqtype ssrnat seq fintype bigop div path
        workload_bound.

Module ResponseTimeIterationFP.

  Import Schedule ResponseTimeAnalysisFP WorkloadBound.

  (* In this section, we define the algorithm of Bertogna and Cirinei's
     response-time analysis for FP scheduling. *)
  Section Analysis.
    
    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> nat.
    Variable task_period: sporadic_task -> nat.
    Variable task_deadline: sporadic_task -> nat.

    (* During the iterations of the algorithm, we pass around pairs
       of tasks and computed response-time bounds. *)
    Let task_with_response_time := (sporadic_task * nat)%type.
    
    Context {Job: eqType}.
    Variable job_cost: Job -> nat.
    Variable job_deadline: Job -> nat.
    Variable job_task: Job -> sporadic_task.

    (* Consider a platform with num_cpus processors, ... *)
    Variable num_cpus: nat.

    (* ..., and priorities based on an FP policy. *)
    Variable higher_priority: fp_policy sporadic_task.

    (* Next we define the fixed-point iteration for computing
       Bertogna's response-time bound of a task set. *)
    
    (* First, given a sequence of pairs R_prev = <..., (tsk_hp, R_hp)> of
       response-time bounds for the higher-priority tasks, we define an
       iteration that computes the response-time bound of the current task:

           R_tsk (0) = task_cost tsk
           R_tsk (step + 1) =  f (R step),

       where f is the response-time recurrence, step is the number of iterations,
       and R_tsk (0) is the initial state. *)
    Definition per_task_rta (tsk: sporadic_task)
                            (R_prev: seq task_with_response_time) (step: nat) :=
      iter step
        (fun t => task_cost tsk +
                  div_floor
                    (total_interference_bound_fp task_cost task_period tsk
                                                R_prev t higher_priority)
                    num_cpus)
        (task_cost tsk).

    (* To ensure that the iteration converges, we will apply per_task_rta
       a "sufficient" number of times: task_deadline tsk - task_cost tsk + 1.
       This corresponds to the time complexity of the iteration. *)
    Definition max_steps (tsk: sporadic_task) := task_deadline tsk - task_cost tsk + 1.
    
    (* Next we compute the response-time bounds for the entire task set.
       Since high-priority tasks may not be schedulable, we allow the
       computation to fail.
       Thus, given the response-time bound of previous tasks, we either
       (a) append the computed response-time bound (tsk, R) of the current task
           to the list of pairs, or,
       (b) return None if the response-time analysis failed. *)
    Definition fp_bound_of_task hp_pairs tsk :=
      if hp_pairs is Some rt_bounds then
        let R := per_task_rta tsk rt_bounds (max_steps tsk) in
          if R <= task_deadline tsk then
            Some (rcons rt_bounds (tsk, R))
          else None
      else None.

    (* The response-time analysis for a given task set is defined
       as a left-fold (reduce) based on the function above.
       This either returns a list of task and response-time bounds, or None. *)
    Definition fp_claimed_bounds (ts: taskset_of sporadic_task) :=
      foldl fp_bound_of_task (Some [::]) ts.

    (* The schedulability test simply checks if we got a list of
       response-time bounds (i.e., if the computation did not fail). *)
    Definition fp_schedulable (ts: taskset_of sporadic_task) :=
      fp_claimed_bounds ts != None.
    
    (* In the following section, we prove several helper lemmas about the
       list of response-time bounds. The results seem trivial, but must be proven
       nonetheless since the list of response-time bounds is computed with
       a specific algorithm and there are no lemmas in the library for that. *)
    Section SimpleLemmas.

      (* First, we show that R_list of the prefix is the prefix of R_list. *)
      Lemma fp_claimed_bounds_rcons_prefix :
        forall ts' hp_bounds tsk1 tsk2 R,
          fp_claimed_bounds (rcons ts' tsk1) = Some (rcons hp_bounds (tsk2, R)) ->
            fp_claimed_bounds ts' = Some hp_bounds.
      Proof.
        intros ts hp_bounds tsk1 tsk2 R SOME.
        rewrite -cats1 in SOME.
        unfold fp_claimed_bounds in *.
        rewrite foldl_cat in SOME.
        simpl in SOME.
        unfold fp_bound_of_task in SOME.
        desf; rewrite Heq; rename H0 into EQ.
        move: EQ => /eqP EQ.
        rewrite eqseq_rcons in EQ.
        move: EQ => /andP [/eqP EQ _].
        by f_equal.
      Qed. 

      (* R_list returns the same tasks as the original task set. *)
      Lemma fp_claimed_bounds_rcons_task :
        forall ts' hp_bounds tsk1 tsk2 R,
          fp_claimed_bounds (rcons ts' tsk1) = Some (rcons hp_bounds (tsk2, R)) ->
            tsk1 = tsk2.
      Proof.
        intros ts hp_bounds tsk1 tsk2 R SOME.
        rewrite -cats1 in SOME.
        unfold fp_claimed_bounds in *.
        rewrite foldl_cat in SOME.
        simpl in SOME.
        unfold fp_bound_of_task in SOME.
        desf; rename H0 into EQ.
        move: EQ => /eqP EQ.
        rewrite eqseq_rcons in EQ.
        move: EQ => /andP [_ /eqP EQ].
        by inversion EQ.
      Qed.

      (* The response-time bounds computed using R_list are based on the per-task
         fixed-point iteration. *)
      Lemma fp_claimed_bounds_rcons_response_time :
        forall ts' hp_bounds tsk R,
          fp_claimed_bounds (rcons ts' tsk) = Some (rcons hp_bounds (tsk, R)) ->
            R = per_task_rta tsk hp_bounds (max_steps tsk). 
      Proof.
        intros ts hp_bounds tsk R SOME.
        rewrite -cats1 in SOME.
        unfold fp_claimed_bounds in SOME.
        rewrite foldl_cat in SOME.
        simpl in SOME.
        unfold fp_bound_of_task in SOME.
        desf; rename H0 into EQ; move: EQ => /eqP EQ.
        rewrite eqseq_rcons in EQ; move: EQ => /andP [/eqP EQ1 /eqP EQ2].
        by inversion EQ2; rewrite EQ1.
      Qed.

      (* If the analysis suceeds, the computed response-time bounds are no larger
         than the deadline. *)
      Lemma fp_claimed_bounds_le_deadline :
        forall ts' rt_bounds tsk R,
          fp_claimed_bounds ts' = Some rt_bounds ->
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
            unfold fp_claimed_bounds in *.
            rewrite foldl_cat /= in SOME.
            unfold fp_bound_of_task in SOME.
            desf; rename H0 into EQ.
            move: EQ => /eqP EQ.
            rewrite eqseq_rcons in EQ.
            move: EQ => /andP [_ /eqP EQ].
            inversion EQ; subst.
            by apply Heq0.
          }
          {
            apply IHts with (rt_bounds := rt_bounds); last by ins.
            by apply fp_claimed_bounds_rcons_prefix in SOME.
          }
        }
      Qed.

      (* If the analysis succeeds, the computed response-time bounds are no smaller
         than the task cost. *)
      Lemma fp_claimed_bounds_ge_cost :
        forall ts' rt_bounds tsk R,
          fp_claimed_bounds ts' = Some rt_bounds ->
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
            unfold fp_claimed_bounds in *.
            rewrite foldl_cat /= in SOME.
            unfold fp_bound_of_task in SOME.
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
            by apply fp_claimed_bounds_rcons_prefix in SOME.
          }
        }
      Qed.

      (* The list contains a response-time bound for every task in the task set. *)
      Lemma fp_claimed_bounds_non_empty :
        forall ts' rt_bounds tsk,
          fp_claimed_bounds ts' = Some rt_bounds ->
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
            unfold fp_claimed_bounds in *.
            rewrite -cats1 foldl_cat in SOME.
            simpl in SOME.
            unfold fp_bound_of_task in *; desf; rename H0 into EQ.
            destruct l; first by ins.
            by rewrite rcons_cons in EQ; inversion EQ.
          }
          split.
          {
            intros IN; rewrite mem_rcons in_cons in IN; move: IN => /orP IN.
            destruct IN as [LAST | FRONT].
            {
              move: LAST => /eqP LAST; subst tsk_i.
              generalize SOME; apply fp_claimed_bounds_rcons_task in SOME; subst tsk_lst'; intro SOME.
              exists R_lst.
              by rewrite mem_rcons in_cons; apply/orP; left.
            }
            {
              apply fp_claimed_bounds_rcons_prefix in SOME.
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
              apply fp_claimed_bounds_rcons_task in SOME; subst.
              by rewrite mem_rcons in_cons; apply/orP; left.
            }
            {
              rewrite mem_rcons in_cons; apply/orP; right.
              exploit (IHts rt_bounds tsk_i);
                [by apply fp_claimed_bounds_rcons_prefix in SOME | intro EX].
              by apply EX; exists R.
            }
          }
        }
      Qed.

      (* Short lemma about unfolding the iteration one step. *)
      Lemma per_task_rta_fold :
        forall tsk rt_bounds,
          task_cost tsk +
           div_floor (total_interference_bound_fp task_cost task_period tsk rt_bounds
                     (per_task_rta tsk rt_bounds (max_steps tsk)) higher_priority) num_cpus
          = per_task_rta tsk rt_bounds (max_steps tsk).+1.
      Proof.
          by done.
      Qed.

    End SimpleLemmas.

    (* In this section, we prove that if the task set is sorted by priority,
       the tasks in fp_claimed_bounds are interfering tasks.  *)
    Section HighPriorityTasks.

      (* Consider a list of previous tasks and a task tsk to be analyzed. *)
      Variable ts_hp: taskset_of sporadic_task.
      Variable tsk: sporadic_task.

      (* Assume that the task set doesn't contain duplicates and is sorted by priority, ... *)
      Hypothesis H_task_set_is_a_set: uniq (rcons ts_hp tsk).
      Hypothesis H_task_set_is_sorted: sorted higher_priority (rcons ts_hp tsk).

      (* ...the priority order is transitive, ...*)
      Hypothesis H_priority_transitive: transitive higher_priority.
      
      (* ... and that the response-time analysis succeeds. *)
      Variable hp_bounds: seq task_with_response_time.
      Variable R: time.
      Hypothesis H_analysis_succeeds: fp_claimed_bounds (rcons ts_hp tsk) = Some (rcons hp_bounds (tsk, R)).
      
      (* Then, the tasks in the prefix of fp_claimed_bounds are exactly interfering tasks
         under FP scheduling.*)
      Lemma fp_claimed_bounds_unzip1 :
        [seq tsk_hp <- rcons ts_hp tsk | is_interfering_task_fp higher_priority tsk tsk_hp] =
          unzip1 hp_bounds.
      Proof.
        rename H_priority_transitive into TRANS,
               H_task_set_is_a_set into UNIQ,
               H_analysis_succeeds into SOME,
               H_task_set_is_sorted into SORT.
        revert tsk hp_bounds R UNIQ SORT SOME.
        induction ts_hp as [| ts_hp' tsk_lst] using last_ind.
        {
          intros tsk hp_bounds R UNIQ SORT SOME; simpl in *.
          unfold is_interfering_task_fp.
          rewrite eq_refl andbF.
          destruct hp_bounds; first by ins.
          unfold fp_claimed_bounds in SOME; inversion SOME; desf.
          by destruct l.
        }
        {
          intros tsk hp_bounds R UNIQ SORTED SOME.
          destruct (lastP hp_bounds) as [| hp_bounds (tsk_lst', R_lst)].
          {
            apply fp_claimed_bounds_rcons_prefix in SOME.
            unfold fp_claimed_bounds in SOME.
            rewrite -cats1 foldl_cat in SOME.
            unfold fp_bound_of_task in SOME.
            inversion SOME; desf.
            by destruct l.
          }
          generalize SOME; apply fp_claimed_bounds_rcons_prefix, fp_claimed_bounds_rcons_task in SOME;
            subst tsk_lst'; intro SOME.
          specialize (IHt tsk_lst hp_bounds R_lst).
          rewrite filter_rcons in IHt.
          unfold is_interfering_task_fp in IHt; rewrite eq_refl andbF in IHt.
          assert (NOTHP: is_interfering_task_fp higher_priority tsk tsk = false).
          {
            by unfold is_interfering_task_fp; rewrite eq_refl andbF.
          } rewrite filter_rcons NOTHP; clear NOTHP.
          assert (HP: is_interfering_task_fp higher_priority tsk tsk_lst).
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
          assert (SHIFT: [seq tsk_hp <- ts_hp' | is_interfering_task_fp
                                                higher_priority tsk tsk_hp] =
                         [seq tsk_hp <- ts_hp' | is_interfering_task_fp
                                                higher_priority tsk_lst tsk_hp]).
          {
            apply eq_in_filter; red.
            unfold is_interfering_task_fp; intros x INx.
            rewrite 2!rcons_uniq mem_rcons in_cons negb_or in UNIQ.
            move: UNIQ => /andP [/andP [NEQ NOTIN] /andP [NOTIN' UNIQ]].
            destruct (x == tsk) eqn:EQtsk;
              first by move: EQtsk => /eqP EQtsk; subst; rewrite INx in NOTIN.
            destruct (x == tsk_lst) eqn:EQlst;
              first by move: EQlst => /eqP EQlst; subst; rewrite INx in NOTIN'.
            rewrite 2!andbT.
            generalize SORTED; intro SORTED'.
            apply order_sorted_rcons with (x0 := x) in SORTED; try (by ins);
              last by rewrite mem_rcons in_cons; apply/orP; right.
            rewrite SORTED.
            apply sorted_rcons_prefix in SORTED'.
            by apply order_sorted_rcons with (x0 := x) in SORTED'.
          } rewrite SHIFT; clear SHIFT.
          apply IHt.
            by rewrite rcons_uniq in UNIQ; move: UNIQ => /andP [_ UNIQ].
            by apply sorted_rcons_prefix in SORTED.
            by apply fp_claimed_bounds_rcons_prefix in SOME.
        }
      Qed.
      
    End HighPriorityTasks.

    (* In this section, we show that the fixed-point iteration converges. *)
    Section Convergence.

      (* Consider any set of higher-priority tasks. *)
      Variable ts_hp: taskset_of sporadic_task.

      (* Assume that the response-time analysis succeeds for the higher-priority tasks. *)
      Variable rt_bounds: seq task_with_response_time.
      Hypothesis H_test_succeeds: fp_claimed_bounds ts_hp = Some rt_bounds.

      (* Consider any task tsk to be analyzed, ... *)
      Variable tsk: sporadic_task.

      (* ... and assume all tasks have valid parameters. *)
      Hypothesis H_valid_task_parameters:
        valid_sporadic_taskset task_cost task_period task_deadline (rcons ts_hp tsk).

      (* To simplify, let f denote the fixed-point iteration. *)
      Let f := per_task_rta tsk rt_bounds.

      (* Assume that f (max_steps tsk) is no larger than the deadline. *)
      Hypothesis H_no_larger_than_deadline: f (max_steps tsk) <= task_deadline tsk.

      (* First, we show that f is monotonically increasing. *)
      Lemma bertogna_fp_comp_f_monotonic :
        forall x1 x2, x1 <= x2 -> f x1 <= f x2.
      Proof.
        unfold valid_sporadic_taskset, is_valid_sporadic_task in *.
        rename H_test_succeeds into SOME,
               H_valid_task_parameters into VALID.
        intros x1 x2 LEx; unfold f, per_task_rta.
        apply fun_mon_iter_mon; [by ins | by ins; apply leq_addr |].
        clear LEx x1 x2; intros x1 x2 LEx.
        unfold div_floor, total_interference_bound_fp.
        rewrite big_seq_cond [\sum_(i <- _ | let '(tsk_other, _) := i in
                                 _ && (tsk_other != tsk))_]big_seq_cond.
        rewrite leq_add2l leq_div2r // leq_sum //.

        intros i; destruct (i \in rt_bounds) eqn:HP; last by rewrite andFb.
        destruct i as [i R]; intros _.
        have GE_COST := (fp_claimed_bounds_ge_cost ts_hp rt_bounds i R).
        have INts := (fp_claimed_bounds_non_empty ts_hp rt_bounds i SOME).
        destruct INts as [_ EX]; exploit EX; [by exists R | intro IN].
        unfold interference_bound_fp; simpl.
        rewrite leq_min; apply/andP; split.
        {
          apply leq_trans with (n := W task_cost task_period i R x1); first by apply geq_minl.
            exploit (VALID i); [by rewrite mem_rcons in_cons IN orbT | ins; des].
            by apply W_monotonic; try (by ins);
              [by apply GE_COST | by apply leqnn].
        }
        {
          apply leq_trans with (n := x1 - task_cost tsk + 1); first by apply geq_minr.
          by rewrite leq_add2r leq_sub2r //.
        }
      Qed.

      (* If the iteration converged at an earlier step, then it remains stable. *)
      Lemma bertogna_fp_comp_f_converges_early :
        (exists k, k <= max_steps tsk /\ f k = f k.+1) ->
        f (max_steps tsk) = f (max_steps tsk).+1.
      Proof.
        by intros EX; des; apply iter_fix with (k := k).
      Qed.

      (* Else, we derive a contradiction. *)
      Section DerivingContradiction.

        (* Assume instead that the iteration continued to diverge. *)
        Hypothesis H_keeps_diverging:
          forall k,
            k <= max_steps tsk -> f k != f k.+1.

        (* By monotonicity, it follows that the value always increases. *)
        Lemma bertogna_fp_comp_f_increases :
          forall k,
            k <= max_steps tsk ->
            f k < f k.+1.
        Proof.
          intros k LT.
          rewrite ltn_neqAle; apply/andP; split.
            by apply H_keeps_diverging.
            by apply bertogna_fp_comp_f_monotonic, leqnSn.
        Qed.

        (* In the end, the response-time bound must exceed the deadline. Contradiction! *)
        Lemma bertogna_fp_comp_rt_grows_too_much :
          forall k,
            k <= max_steps tsk ->
            f k > k + task_cost tsk - 1.
        Proof.
          rename H_valid_task_parameters into TASK_PARAMS.
          unfold valid_sporadic_taskset, is_valid_sporadic_task in *; des.
          exploit (TASK_PARAMS tsk);
            [by rewrite mem_rcons in_cons eq_refl orTb | intro PARAMS; des].
          induction k.
          {
            intros _; rewrite add0n -addn1 subh1;
              first by rewrite -addnBA // subnn addn0 /= leqnn.
            by apply PARAMS.
          }
          {
            intros LT.
            specialize (IHk (ltnW LT)).
            apply leq_ltn_trans with (n := f k);
              last by apply bertogna_fp_comp_f_increases, ltnW.
            rewrite -addn1 -addnA [1 + _]addnC addnA -addnBA // subnn addn0.
            rewrite -(ltn_add2r 1) in IHk.
            rewrite subh1 in IHk; last first.
            {
              apply leq_trans with (n := task_cost tsk); last by apply leq_addl.
              by apply PARAMS.
            }
            by rewrite -addnBA // subnn addn0 addn1 ltnS in IHk.
          }  
        Qed.

      End DerivingContradiction.
      
      (* Using the lemmas above, we prove the convergence of the iteration after max_steps. *)
      Lemma per_task_rta_converges:
        f (max_steps tsk) = f (max_steps tsk).+1.
      Proof.
        rename H_no_larger_than_deadline into LE,
               H_valid_task_parameters into TASK_PARAMS.
        unfold valid_sporadic_taskset, is_valid_sporadic_task in *; des.
       
        (* Either f converges by the deadline or not. *)
        destruct ([exists k in 'I_(max_steps tsk).+1, f k == f k.+1]) eqn:EX.
        {
          move: EX => /exists_inP EX; destruct EX as [k _ ITERk].
          apply bertogna_fp_comp_f_converges_early.
          by exists k; split; [by rewrite -ltnS; apply ltn_ord | by apply/eqP].
        }

        (* If not, then we reach a contradiction *)
        apply negbT in EX; rewrite negb_exists_in in EX.
        move: EX => /forall_inP EX.
        rewrite leqNgt in LE; move: LE => /negP LE.
        exfalso; apply LE.
        have TOOMUCH := bertogna_fp_comp_rt_grows_too_much _ (max_steps tsk).
        exploit TOOMUCH; [| by apply leqnn |].
        {
          intros k LEk; rewrite -ltnS in LEk.
          by exploit (EX (Ordinal LEk)); [by done | intro DIFF].
        }
        unfold max_steps at 1.
        exploit (TASK_PARAMS tsk);
          [by rewrite mem_rcons in_cons eq_refl orTb | intro PARAMS; des].
        rewrite -addnA [1 + _]addnC addnA -addnBA // subnn addn0.
        rewrite subh1; last by apply PARAMS2.
        by rewrite -addnBA // subnn addn0.
      Qed.
      
    End Convergence.
    
    Section MainProof.

      (* Consider a task set ts. *)
      Variable ts: taskset_of sporadic_task.
      
      (* Assume that higher_eq_priority is a total order.
         TODO: it doesn't have to be total over the entire domain, but
         only within the task set.
         But to weaken the hypothesis, we need to re-prove some lemmas
         from ssreflect. *)
      Hypothesis H_transitive: transitive higher_priority.
      Hypothesis H_unique_priorities: antisymmetric higher_priority.
      Hypothesis H_total: total higher_priority.

      (* Assume the task set has no duplicates, ... *)
      Hypothesis H_ts_is_a_set: uniq ts.

      (* ...all tasks have valid parameters, ... *)
      Hypothesis H_valid_task_parameters:
        valid_sporadic_taskset task_cost task_period task_deadline ts.

      (* ...restricted deadlines, ...*)
      Hypothesis H_restricted_deadlines:
        forall tsk, tsk \in ts -> task_deadline tsk <= task_period tsk.

      (* ...and tasks are ordered by increasing priorities. *)
      Hypothesis H_sorted_ts: sorted higher_priority ts.

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
      
      (* Then, consider any platform with at least one CPU such that...*)
      Variable sched: schedule num_cpus arr_seq.
      Hypothesis H_at_least_one_cpu :
        num_cpus > 0.

      (* ...jobs only execute after they arrived and no longer
         than their execution costs,... *)
      Hypothesis H_jobs_must_arrive_to_execute:
        jobs_must_arrive_to_execute sched.
      Hypothesis H_completed_jobs_dont_execute:
        completed_jobs_dont_execute job_cost sched.

      (* ...and do not execute in parallel (required by the workload bound). *)
      Hypothesis H_no_parallelism:
        jobs_dont_execute_in_parallel sched.

      (* Assume the platform satisfies the global scheduling invariant. *)
      Hypothesis H_global_scheduling_invariant:
        FP_scheduling_invariant_holds job_cost job_task num_cpus sched ts higher_priority.

      Let no_deadline_missed_by_task (tsk: sporadic_task) :=
        task_misses_no_deadline job_cost job_deadline job_task sched tsk.
      Let no_deadline_missed_by_job :=
        job_misses_no_deadline job_cost job_deadline sched.
      Let response_time_bounded_by (tsk: sporadic_task) :=
        is_response_time_bound_of_task job_cost job_task tsk sched.
          
      (* In the following theorem, we prove that any response-time bound contained
         in fp_claimed_bounds is safe. The proof follows by induction on the task set:

           Induction hypothesis: all higher-priority tasks have safe response-time bounds.
           Inductive step: We prove that the response-time bound of the current task is safe.

         Note that the inductive step is a direct application of the main Theorem from
         bertogna_fp_theory.v. *)
      Theorem fp_analysis_yields_response_time_bounds :
        forall tsk R,
          (tsk, R) \In fp_claimed_bounds ts ->
          response_time_bounded_by tsk R.
      Proof.
        rename H_valid_job_parameters into JOBPARAMS, H_valid_task_parameters into TASKPARAMS,
               H_restricted_deadlines into RESTR, H_completed_jobs_dont_execute into COMP,
               H_jobs_must_arrive_to_execute into MUSTARRIVE, H_sorted_ts into SORT,
               H_global_scheduling_invariant into INVARIANT, H_transitive into TRANS,
               H_unique_priorities into UNIQ, H_total into TOTAL,
               H_all_jobs_from_taskset into ALLJOBS, H_ts_is_a_set into SET.
        clear ALLJOBS.
        intros tsk R MATCH.
        assert (SOME: exists hp_bounds, fp_claimed_bounds ts = Some hp_bounds /\ (tsk, R) \in hp_bounds).
        {
          destruct (fp_claimed_bounds ts); last by done.
          by exists l; split.
        } clear MATCH; des.
        revert hp_bounds tsk R SOME SOME0.
        unfold fp_schedulable, fp_claimed_bounds in *.
        induction ts as [| ts' tsk_i IH] using last_ind.
        {
          intros hp_bounds tsk R SOME IN.
          by inversion SOME; subst; rewrite in_nil in IN.
        }
        {
          intros hp_bounds tsk R SOME IN j JOBj.
          destruct (lastP hp_bounds) as [| hp_bounds (tsk_lst, R_lst)];
            first by rewrite in_nil in IN.
          rewrite mem_rcons in_cons in IN; move: IN => /orP IN.
          destruct IN as [LAST | BEGINNING]; last first.
          {
            apply IH with (hp_bounds := hp_bounds) (tsk := tsk); try (by ins).
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
              generalize SOME; apply fp_claimed_bounds_rcons_task in SOME; subst tsk_i; intro SOME.
              assert (HP: higher_priority tsk_lst tsk0 = false).
              {
                apply order_sorted_rcons with (x := tsk0) in SORT; [|by ins | by ins].
                apply negbTE; apply/negP; unfold not; intro BUG.
                exploit UNIQ; [by apply/andP; split; [by apply SORT | by ins] | intro EQ].
                by rewrite rcons_uniq -EQ IN0 in SET.
              }              
              by rewrite HP 2!andFb 2!addn0 in INV.
            }
            by apply fp_claimed_bounds_rcons_prefix in SOME.
          }
          {
            move: LAST => /eqP LAST.
            inversion LAST as [[EQ1 EQ2]].
            rewrite -> EQ1 in *; rewrite -> EQ2 in *; clear EQ1 EQ2 LAST.
            generalize SOME; apply fp_claimed_bounds_rcons_task in SOME; subst tsk_i; intro SOME.
            generalize SOME; apply fp_claimed_bounds_rcons_prefix in SOME; intro SOME'.
            have BOUND := bertogna_cirinei_response_time_bound_fp.
            unfold is_response_time_bound_of_task in BOUND.
            apply BOUND with (task_cost := task_cost) (task_period := task_period)
                  (task_deadline := task_deadline) (job_deadline := job_deadline) (tsk := tsk_lst)
                  (job_task := job_task) (ts := rcons ts' tsk_lst) (hp_bounds := hp_bounds)
                               (higher_eq_priority := higher_priority); clear BOUND; try (by ins).
            by rewrite mem_rcons in_cons eq_refl orTb.
            by apply fp_claimed_bounds_unzip1 with (R := R_lst).
            {
              intros hp_tsk R0 HP j0 JOB0.
              apply IH with (hp_bounds := hp_bounds) (tsk := hp_tsk); try (by ins).
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
                assert (NOINTERF: higher_priority tsk_lst tsk0 = false).
                {
                  apply order_sorted_rcons with (x := tsk0) in SORT; [|by ins | by ins].
                  apply negbTE; apply/negP; unfold not; intro BUG.
                  exploit UNIQ; [by apply/andP; split; [by apply BUG | by ins] | intro EQ].
                  by rewrite rcons_uniq EQ IN0 in SET.
                }
                by rewrite NOINTERF 2!andFb addn0 in INV.
              }
            }
            by ins; apply fp_claimed_bounds_ge_cost with (ts' := ts') (rt_bounds := hp_bounds).
            by ins; apply fp_claimed_bounds_le_deadline with (ts' := ts') (rt_bounds := hp_bounds).
            {
              rewrite [R_lst](fp_claimed_bounds_rcons_response_time ts' hp_bounds tsk_lst); last by ins.
              rewrite per_task_rta_fold.
              apply per_task_rta_converges with (ts_hp := ts'); try (by done).
              apply fp_claimed_bounds_le_deadline with (ts' := rcons ts' tsk_lst)
                                            (rt_bounds := rcons hp_bounds (tsk_lst, R_lst));
                first by apply SOME'.
              rewrite mem_rcons in_cons; apply/orP; left; apply/eqP.
              f_equal; symmetry.
              by apply fp_claimed_bounds_rcons_response_time with (ts' := ts'). 
            }
          }
        }
      Qed.

      (* Therefore, if the schedulability test suceeds, ...*)
      Hypothesis H_test_succeeds: fp_schedulable ts.
      
      (*..., no task misses its deadline. *)
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

        move => tsk INtsk j JOBtsk.
        have RLIST := (fp_analysis_yields_response_time_bounds).
        have NONEMPTY := (fp_claimed_bounds_non_empty ts).
        have DL := (fp_claimed_bounds_le_deadline ts).

        destruct (fp_claimed_bounds ts) as [rt_bounds |]; last by ins.
        exploit (NONEMPTY rt_bounds tsk); [by ins | intros [EX _]; specialize (EX INtsk); des].
        exploit (RLIST tsk R); [by ins | by apply JOBtsk | intro COMPLETED].
        exploit (DL rt_bounds tsk R); [by ins | by ins | clear DL; intro DL].
        
        rewrite eqn_leq; apply/andP; split; first by apply cumulative_service_le_job_cost.
        apply leq_trans with (n := service sched j (job_arrival j + R)); last first.
        {
          unfold valid_sporadic_taskset, is_valid_sporadic_task in *.
          apply extend_sum; rewrite // leq_add2l.
          specialize (JOBPARAMS j); des; rewrite JOBPARAMS1.
          by rewrite JOBtsk.
        }
        rewrite leq_eqVlt; apply/orP; left; rewrite eq_sym.
        by apply COMPLETED.
      Qed.

      (* For completeness, since all jobs of the arrival sequence
         are spawned by the task set, we also conclude that no job in
         the schedule misses its deadline. *)
      Theorem jobs_schedulable_by_fp_rta :
        forall (j: JobIn arr_seq), no_deadline_missed_by_job j.
      Proof.
        intros j.
        have SCHED := taskset_schedulable_by_fp_rta.
        unfold no_deadline_missed_by_task, task_misses_no_deadline in *.
        apply SCHED with (tsk := job_task j); last by done.
        by apply H_all_jobs_from_taskset.
      Qed.
      
    End MainProof.

  End Analysis.

End ResponseTimeIterationFP.