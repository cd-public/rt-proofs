Require Import workload Vbase job task schedule task_arrival response_time
               schedulability util_divround util_lemmas
               ssreflect ssrbool eqtype ssrnat seq div fintype bigop path.
Module WorkloadBoundGuan.
  Import Job SporadicTaskset Schedule SporadicTaskArrival ResponseTime         Schedulability Workload.

  
  Section WorkloadBoundCarry.

    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> nat.
    Variable task_period: sporadic_task -> nat.

    (* Let tsk be any task with response-time bound R_tsk,
       and consider an interval of interest with length delta. *)
    Variable tsk: sporadic_task.
    Variable R_tsk: time.
    Variable delta: time.

    Let e := task_cost tsk.
    Let p := task_period tsk.

    (* Next, we define the workload bounds W_NC and W_CI
       used in Guan et al.'s response-time analysis. *)
    Definition max_jobs_NC := div_floor delta p.
    Definition max_jobs_CI := div_floor (delta - e) p.
    
    Definition W_NC :=
        max_jobs_NC * e + minn (delta %% p) e.

    Definition W_CI :=
        max_jobs_CI * e + e +
          minn (e - 1) ((delta - e) %% p - (p - R_tsk)).
    
  End WorkloadBoundCarry.

  Section BasicLemmasCarry.

    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> nat.
    Variable task_period: sporadic_task -> nat.

    (* Let tsk be any task with period > 0. *)
    Variable tsk: sporadic_task.
    Hypothesis period_positive: task_period tsk > 0.

    (* Let R be a response-time bound for tsk. *)
    Variable R: time.

    Let workload_bound_NC := W_NC task_cost task_period tsk.
    Let workload_bound_CI := W_CI task_cost task_period tsk R.

    (* Then, both workload bounds W_NC and W_CI are monotonically increasing. *) 
    Lemma W_NC_monotonic :
      forall t1 t2,
        t1 <= t2 ->
        workload_bound_NC t1 <= workload_bound_NC t2.
    Proof.
      intros t1 t2 LEt.
      unfold workload_bound_NC, W_NC, max_jobs_NC, div_floor.
      set e := task_cost tsk; set p := task_period tsk.
     
      generalize dependent t2; rewrite leq_as_delta.
      induction delta; first by rewrite addn0 leqnn.
      {
        apply (leq_trans IHdelta).

        (* Prove special case for p <= 1. *)
        destruct (leqP p 1) as [LTp | GTp].
        {
          rewrite leq_eqVlt in LTp; move: LTp => /orP LTp; des;
            last by rewrite ltnS in LTp; apply (leq_trans period_positive) in LTp. 
          {
            move: LTp => /eqP LTp; rewrite LTp 2!modn1 2!divn1.
            rewrite min0n leq_add2r leq_mul2r; apply/orP; right.
            by rewrite -addn1 addnA leq_addr.
          }
        }
        (* Harder case: p > 1. *)
        {
          assert (EQ: t1 + delta.+1 = (t1 + delta).+1).
          {
            by rewrite -addn1 addnA addn1.
          } rewrite -> EQ in *; clear EQ.
         
          have DIV := divSn_cases (t1 + delta) p GTp; des.
          {
            rewrite DIV leq_add2l -DIV0 leq_min; apply/andP; split;
              last by apply geq_minr.
            by apply ltnW; rewrite addn1 ltnS; apply geq_minl.           
          }
          {
            rewrite -DIV mulnDl mul1n; unfold minn at 2.
            destruct ((t1 + delta).+1 %% p < e) eqn:MIN;
              first by rewrite -[_ + _]addn0 leq_add // leq_add2l geq_minr.
            rewrite -addnA leq_add2l.
            by apply leq_trans with (n := e);
              [by apply geq_minr | by apply leq_addr].
          }
        }
      }
    Qed.

   Lemma W_CI_monotonic :
     forall t1 t2,
       t1 <= t2 ->
       workload_bound_CI t1 <= workload_bound_CI t2.
   Proof.
     intros t1 t2 LEt.
     unfold workload_bound_CI, W_CI, max_jobs_CI, div_floor.
     set e := task_cost tsk; set p := task_period tsk.
     rewrite 2![_ + e]addnC; rewrite -2!addnA leq_add2l.
     generalize dependent t2; rewrite leq_as_delta.
     induction delta; first by rewrite addn0 leqnn.
     {
       apply (leq_trans IHdelta).

       (* Prove special case for p <= 1. *)
       destruct (leqP p 1) as [LTp | GTp].
       {
         rewrite leq_eqVlt in LTp; move: LTp => /orP LTp; des;
           last by rewrite ltnS in LTp; apply (leq_trans period_positive) in LTp. 
         move: LTp => /eqP LTp; rewrite LTp 2!modn1 2!divn1.
         rewrite sub0n minn0 2!addn0 leq_mul2r; apply/orP; right.
         by rewrite leq_sub2r // -addn1 addnA leq_addr.
       }
       (* Harder case: p > 1. *)
       {
         destruct (e >= t1 + delta) eqn:CMPt1.
         {
           unfold leq in CMPt1; move: CMPt1 => /eqP CMPt1.
           by rewrite CMPt1 div0n mul0n add0n mod0n sub0n minn0.
         }
         apply negbT in CMPt1; rewrite -ltnNge in CMPt1.
         
         assert (EQ: t1 + delta.+1 - e = (t1 + delta - e).+1).
         {
           rewrite -[(t1 + delta - e).+1]addn1.
           rewrite [_+1]addnC addnBA; last by apply ltnW.
           by rewrite [1 + _]addnC -addnA addn1.
         } rewrite -> EQ in *; clear EQ CMPt1.
         
         have DIV := divSn_cases (t1 + delta - e) p GTp; des.
         {
           rewrite DIV leq_add2l -DIV0 leq_min; apply/andP; split;
             first by apply geq_minl.
           apply leq_trans with (n := (t1 + delta - e) %%p - (p - R));
             first by apply geq_minr.
           by rewrite leq_sub2r // addn1.
         }
         {
           rewrite -DIV mulnDl mul1n -addnA leq_add2l; unfold minn at 2.
           destruct (e - 1 < (t1 + delta - e).+1 %% p - (p - R)) eqn:MIN;
             first by rewrite -[minn _ _]add0n leq_add // geq_minl.
           destruct e; first by rewrite sub0n min0n.
           rewrite -addn1 -addnBA // subnn addn0.
           by apply leq_trans with (n := e);
             [by apply geq_minl | by rewrite -addnA leq_addr].
         }
       }
     }
   Qed.

  End BasicLemmasCarry.

  Section ProofWorkloadBound.

    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> nat.
    Variable task_period: sporadic_task -> nat.
    Variable task_deadline: sporadic_task -> nat.
    
    Context {Job: eqType}.
    Variable job_cost: Job -> nat.
    Variable job_task: Job -> sporadic_task.
    Variable job_deadline: Job -> nat.

    Variable arr_seq: arrival_sequence Job.

    (* Assume that all jobs have valid parameters *)
    Hypothesis H_jobs_have_valid_parameters :
      forall (j: JobIn arr_seq),
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j.
    
    Variable num_cpus: nat.
    Variable rate: Job -> processor num_cpus -> nat.
    Variable schedule_of_platform: schedule num_cpus arr_seq -> Prop.

    (* Assume any schedule of a given platform. *)
    Variable sched: schedule num_cpus arr_seq.
    Hypothesis sched_of_platform: schedule_of_platform sched.

    (* Assumption: jobs only execute if they arrived.
       This is used to eliminate jobs that arrive after end of the interval t1 + delta. *)
    Hypothesis H_jobs_must_arrive_to_execute:
      jobs_must_arrive_to_execute sched.

    (* Assumption: jobs do not execute after they completed.
       This is used to eliminate jobs that complete before the start of the interval t1. *)
    Hypothesis H_completed_jobs_dont_execute:
      completed_jobs_dont_execute job_cost rate sched.

    (* Assumptions:
         1) A job does not execute in parallel.
         2) The service rate of the platform is at most 1.
       This is required to use interval lengths as a measure of service. *)
    Hypothesis H_no_parallelism:
      jobs_dont_execute_in_parallel sched.
    Hypothesis H_rate_at_most_one :
      forall j cpu, rate j cpu <= 1.

    (* Assumption: sporadic task model.
       This is necessary to conclude that consecutive jobs ordered by arrival times
       are separated by at least 'period' times units. *)
    Hypothesis H_sporadic_tasks: sporadic_task_model task_period arr_seq job_task.

    (* Before starting the proof, let's give simpler names to the definitions. *)
    Let job_has_completed_by := completed job_cost rate sched.
    Let no_deadline_misses_by (tsk: sporadic_task) (t: time) :=
      task_misses_no_deadline_before job_cost job_deadline job_task
                                     rate sched tsk t.
    Let workload_of (tsk: sporadic_task) (t1 t2: time) :=
      workload job_task rate sched tsk t1 t2.

    (* Now we define the theorem. Let tsk be any task in the taskset. *)
    Variable tsk: sporadic_task.

    (* Assumption: the task must have valid parameters:
         a) period > 0 (used in divisions)
         b) deadline of the jobs = deadline of the task
         c) cost <= period
            (used to prove that the distance between the first and last
             jobs is at least (cost + n*period), where n is the number
             of middle jobs. If cost >> period, the claim does not hold
             for every task set. *)
    Hypothesis H_valid_task_parameters:
      is_valid_sporadic_task task_cost task_period task_deadline tsk.

    (* Assumption: the task must have a restricted deadline.
       This is required to prove that n_k (max_jobs) from Bertogna
       and Cirinei's formula accounts for at least the number of
       middle jobs (i.e., number of jobs - 2 in the worst case). *)
    Hypothesis H_restricted_deadline: task_deadline tsk <= task_period tsk.
      
    (* Consider an interval [t1, t1 + delta), with no deadline misses. *)
    Variable t1 delta: time.
    Hypothesis H_no_deadline_misses_during_interval: no_deadline_misses_by tsk (t1 + delta).

    (* Assume that a response-time bound R_tsk for that task in any
       schedule of this processor platform is also given,
       such that R_tsk >= task_cost tsk. *)
    Variable R_tsk: time.

    Hypothesis H_response_time_ge_cost: R_tsk >= task_cost tsk.

    Hypothesis H_response_time_bound :    
      forall (j: JobIn arr_seq),
      job_task j = tsk ->
      job_arrival j + R_tsk < t1 + delta ->
      job_has_completed_by j (job_arrival j + R_tsk).
   
   Section GuanNoCarry.
       
      Let is_carry_in_job := carried_in job_cost rate sched.

      (* Assume that task tsk has no carry-in job in the interval delta. *)
      Hypothesis H_no_carry_in:
        ~ exists (j: JobIn arr_seq),
          job_task j = tsk /\ is_carry_in_job j t1.
        
      Let workload_bound := W_NC task_cost task_period.

      (* Then, tsk's workload is bounded by W_NC, according to Guan et al.'s
         response-time analysis. *)
      Theorem workload_bounded_by_W_NC :
        workload_of tsk t1 (t1 + delta) <= workload_bound tsk delta.
      Proof.
        rename H_jobs_have_valid_parameters into job_properties,
               H_no_deadline_misses_during_interval into no_dl_misses,
               H_valid_task_parameters into task_properties,
               H_completed_jobs_dont_execute into COMP.
        unfold valid_sporadic_job, valid_realtime_job, restricted_deadline_model,
               valid_sporadic_taskset, is_valid_sporadic_task, sporadic_task_model,
               workload_of, no_deadline_misses_by,
               workload_bound, W_NC in *; ins; des.

        (* Simplify names *)
        set t2 := t1 + delta.
        set n_k := max_jobs_NC task_period tsk delta.

        (* Use the definition of workload based on list of jobs. *)
        rewrite workload_eq_workload_joblist; unfold workload_joblist.
        
        (* Identify the subset of jobs that actually cause interference *)
        set interfering_jobs :=
          filter (fun (x: JobIn arr_seq) =>
                    (job_task x == tsk) && (service_during rate sched x t1 t2 != 0))
                      (jobs_scheduled_between sched t1 t2).
    
        (* Remove the elements that we don't care about from the sum *)
        assert (SIMPL:
          \sum_(i <- jobs_scheduled_between sched t1 t2 | job_task i == tsk)
             service_during rate sched i t1 t2 =
          \sum_(i <- interfering_jobs) service_during rate sched i t1 t2).
        {
          unfold interfering_jobs.
          rewrite (bigID (fun x => service_during rate sched x t1 t2 == 0)) /=.
          rewrite (eq_bigr (fun x => 0)); last by move => j_i /andP JOBi; des; apply /eqP.
          rewrite big_const_seq iter_addn mul0n add0n add0n.
          by rewrite big_filter.
        } rewrite SIMPL; clear SIMPL.

        (* Remember that for any job of tsk, service <= task_cost tsk *)
        assert (LTserv: forall j_i (INi: j_i \in interfering_jobs),
                          service_during rate sched j_i t1 t2 <= task_cost tsk).
        {
          ins; move: INi; rewrite mem_filter; move => /andP xxx; des.
          move: xxx; move => /andP JOBi; des; clear xxx0 JOBi0.
          have PROP := job_properties j_i; des.
          move: JOBi => /eqP JOBi; rewrite -JOBi.
          apply leq_trans with (n := job_cost j_i); last by ins. 
          by apply service_interval_le_cost.
        }

        (* Order the sequence of interfering jobs by arrival time, so that
           we can identify the first and last jobs. *)
        set order := fun (x y: JobIn arr_seq) => job_arrival x <= job_arrival y.
        set sorted_jobs := (sort order interfering_jobs).
        assert (SORT: sorted order sorted_jobs);
          first by apply sort_sorted; unfold total, order; ins; apply leq_total.
        rewrite (eq_big_perm sorted_jobs) /=; last by rewrite -(perm_sort order).
   
        (* Remember that both sequences have the same set of elements *)
        assert (INboth: forall x, (x \in interfering_jobs) = (x \in sorted_jobs)).
          by apply perm_eq_mem; rewrite -(perm_sort order).
          
        (* Find some dummy element to use in the nth function *)
        destruct (size sorted_jobs == 0) eqn:SIZE0;
          first by move: SIZE0 =>/eqP SIZE0; rewrite (size0nil SIZE0) big_nil.
        apply negbT in SIZE0; rewrite -lt0n in SIZE0.
        assert (EX: exists elem: JobIn arr_seq, True); des.
          destruct sorted_jobs; [by rewrite ltn0 in SIZE0 | by exists s].
        clear EX SIZE0.

        (* Remember that the jobs are ordered by arrival. *)
        assert (ALL: forall i (LTsort: i < (size sorted_jobs).-1),
                       order (nth elem sorted_jobs i) (nth elem sorted_jobs i.+1)).
        by destruct sorted_jobs; [by ins| by apply/pathP; apply SORT].
        
        (* Now we start the proof. First, we show that the workload bound
           holds if n_k is no larger than the number of interferings jobs. *)
        destruct (size sorted_jobs <= n_k) eqn:NUM.
        {
          rewrite -[\sum_(_ <- _ | _) _]addn0 leq_add //.
          apply leq_trans with (n := \sum_(x <- sorted_jobs) task_cost tsk);
            last by rewrite big_const_seq iter_addn addn0 mulnC leq_mul2r; apply/orP; right.
          {
            rewrite [\sum_(_ <- _) service_during _ _ _ _ _]big_seq_cond.
            rewrite [\sum_(_ <- _) task_cost _]big_seq_cond.
            by apply leq_sum; intros j_i; move/andP => xxx; des; apply LTserv; rewrite INboth.
          }
        }
        apply negbT in NUM; rewrite -ltnNge in NUM.

        (* Now we index the sum to access the first and last elements. *)
        rewrite (big_nth elem).

        (* First and last only exist if there are at least 2 jobs. Thus, we must show
           that the bound holds for the empty list. *)
        destruct (size sorted_jobs) eqn:SIZE; first by rewrite big_geq.
        rewrite SIZE.
        
        (* Let's derive some properties about the first element. *)
        exploit (mem_nth elem); last intros FST.
          by instantiate (1:= sorted_jobs); instantiate (1 := 0); rewrite SIZE.
        move: FST; rewrite -INboth mem_filter; move => /andP FST; des.
        move: FST => /andP FST; des; move: FST => /eqP FST.
        rename FST0 into FSTin, FST into FSTtask, FST1 into FSTserv.

        (* Now we show that the bound holds for a singleton set of interfering jobs. *)
        destruct n.
        {
          destruct n_k eqn:EQnk; last by ins.
          {
            rewrite mul0n add0n big_nat_recl // big_geq // addn0.
            unfold n_k, max_jobs_NC, div_floor in EQnk.
            rewrite -subndiv_eq_mod EQnk mul0n subn0.
            rewrite leq_min; apply/andP; split; last first.
            {
              apply leq_trans with (n := job_cost (nth elem sorted_jobs 0));
                first by apply service_interval_le_cost.
              by rewrite -FSTtask; have PROP := job_properties (nth elem sorted_jobs 0); des.
            }
            {
              apply leq_trans with (n := \sum_(t1 <= t < t2) 1).
                by apply leq_sum; ins; apply service_at_le_max_rate.
                by unfold t2; rewrite big_const_nat iter_addn mul1n addn0 addnC -addnBA// subnn addn0.
            }
          }
        } rewrite [nth]lock /= -lock in ALL.
    
        (* Knowing that we have at least two elements, we take first and last out of the sum *) 
        rewrite [nth]lock big_nat_recl // big_nat_recr // /= -lock.
        rewrite addnA addnC addnA.
        set j_fst := (nth elem sorted_jobs 0).
        set j_lst := (nth elem sorted_jobs n.+1).
                       
        (* Now we infer some facts about how first and last are ordered in the timeline *)
        assert (INfst: j_fst \in interfering_jobs).
          by unfold j_fst; rewrite INboth; apply mem_nth; destruct sorted_jobs; ins.
        move: INfst; rewrite mem_filter; move => /andP INfst; des.
        move: INfst => /andP INfst; des.

        assert (INlst: j_lst \in interfering_jobs).
        {
            by unfold j_lst; rewrite INboth; apply mem_nth; rewrite SIZE.
        }
        move: INlst; rewrite mem_filter; move => /andP INlst; des.
        move: INlst => /andP INlst; des.
        
        assert (AFTERt1: t1 <= job_arrival j_fst).
        {
          rewrite leqNgt; apply /negP; unfold not; intro LTt1.
          apply H_no_carry_in; exists j_fst; split; first by apply/eqP.
          unfold is_carry_in_job, carried_in; apply/andP; split; first by done.
          unfold completed_jobs_dont_execute, completed in *.
          apply/negP; intro COMPLETED.
          specialize (COMP j_fst t2); rewrite leqNgt in COMP.
          move: COMP => /negP COMP; apply COMP.
          unfold service; rewrite -> big_cat_nat with (n := t1);
            [simpl | by done | by apply leq_addr].
          move: COMPLETED => /eqP COMPLETED; rewrite -COMPLETED.
          apply leq_trans with (n := service rate sched j_fst t1 + 1);
            first by rewrite addn1.
          by rewrite leq_add2l lt0n.
        }

        assert (AFTERt1': t1 <= job_arrival j_lst).
        {
          rewrite leqNgt; apply /negP; unfold not; intro LTt1.
          apply H_no_carry_in; exists j_lst; split; first by apply/eqP.
          unfold is_carry_in_job, carried_in; apply/andP; split; first by done.
          unfold completed_jobs_dont_execute, completed in *.
          apply/negP; intro COMPLETED.
          specialize (COMP j_lst t2); rewrite leqNgt in COMP.
          move: COMP => /negP COMP; apply COMP.
          unfold service; rewrite -> big_cat_nat with (n := t1);
            [simpl | by done | by apply leq_addr].
          move: COMPLETED => /eqP COMPLETED; rewrite -COMPLETED.
          apply leq_trans with (n := service rate sched j_lst t1 + 1);
            first by rewrite addn1.
          by rewrite leq_add2l lt0n.
        }

        assert (BEFOREt2: job_arrival j_lst < t2).
        {
          rewrite leqNgt; apply/negP; unfold not; intro LT2.
          assert (LTsize: n.+1 < size sorted_jobs).
            by destruct sorted_jobs; ins; rewrite SIZE; apply ltnSn.
          apply (mem_nth elem) in LTsize; rewrite -INboth in LTsize.
          rewrite -/interfering_jobs mem_filter in LTsize.
          move: LTsize => /andP [LTsize _]; des.
          move: LTsize => /andP [_ SERV].
          move: SERV => /eqP SERV; apply SERV.
          by unfold service_during; rewrite sum_service_before_arrival.
        }

        assert (BEFOREarr: job_arrival j_fst <= job_arrival j_lst).
        {
          unfold j_fst, j_lst; rewrite -[n.+1]add0n.
          apply prev_le_next; last by rewrite add0n SIZE leqnn.
          by unfold order in ALL; intro i; rewrite SIZE; apply ALL.
        }
        
        (* Now we upper-bound the service of the middle jobs. *)
        assert (BOUNDmid: \sum_(0 <= i < n)
                           service_during rate sched (nth elem sorted_jobs i.+1) t1 t2 <=
                             n * task_cost tsk).
        {
          apply leq_trans with (n := n * task_cost tsk);
            last by rewrite leq_mul2l; apply/orP; right. 
          apply leq_trans with (n := \sum_(0 <= i < n) task_cost tsk);
            last by rewrite big_const_nat iter_addn addn0 mulnC subn0.
          rewrite big_nat_cond [\sum_(0 <= i < n) task_cost _]big_nat_cond.
          apply leq_sum; intros i; rewrite andbT; move => /andP LT; des.
          by apply LTserv; rewrite INboth mem_nth // SIZE ltnS leqW.
        }

        (* Conclude that the distance between first and last is at least n + 1 periods,
           where n is the number of middle jobs. *)
        assert (DIST: job_arrival j_lst - job_arrival j_fst >= n.+1 * (task_period tsk)).
        {
          assert (EQnk: n.+1=(size sorted_jobs).-1); first by rewrite SIZE. 
          unfold j_fst, j_lst; rewrite EQnk telescoping_sum; last by rewrite SIZE.
          rewrite -[_ * _ tsk]addn0 mulnC -iter_addn -{1}[_.-1]subn0 -big_const_nat. 
          rewrite big_nat_cond [\sum_(0 <= i < _)(_-_)]big_nat_cond.
          apply leq_sum; intros i; rewrite andbT; move => /andP LT; des.
          {
            (* To simplify, call the jobs 'cur' and 'next' *)
            set cur := nth elem sorted_jobs i.
            set next := nth elem sorted_jobs i.+1.
            clear BOUNDmid LT LTserv j_fst j_lst
                  INfst INfst0 INfst1 INlst INlst0 INlst1
                  BEFOREarr AFTERt1 AFTERt1' BEFOREt2 FSTserv FSTtask FSTin.

            (* Show that cur arrives earlier than next *)
            assert (ARRle: job_arrival cur <= job_arrival next).
            {
              unfold cur, next; rewrite -addn1; apply prev_le_next; first by rewrite SIZE.
              by apply leq_trans with (n := i.+1); try rewrite addn1.
            }
             
            (* Show that both cur and next are in the arrival sequence *)
            assert (INnth: cur \in interfering_jobs /\
                           next \in interfering_jobs).
              rewrite 2!INboth; split.
              by apply mem_nth, (ltn_trans LT0); destruct sorted_jobs; ins.
              by apply mem_nth; destruct sorted_jobs; ins.
            rewrite 2?mem_filter in INnth; des.

            (* Use the sporadic task model to conclude that cur and next are separated
               by at least (task_period tsk) units. Of course this only holds if cur != next.
               Since we don't know much about the list (except that it's sorted), we must
               also prove that it doesn't contain duplicates. *)
            assert (CUR_LE_NEXT: job_arrival cur + task_period (job_task cur) <= job_arrival next).
            {
              apply H_sporadic_tasks; last by ins.
              unfold cur, next, not; intro EQ; move: EQ => /eqP EQ.
              rewrite nth_uniq in EQ; first by move: EQ => /eqP EQ; intuition.
                by apply ltn_trans with (n := (size sorted_jobs).-1); destruct sorted_jobs; ins.
                by destruct sorted_jobs; ins.
                by rewrite sort_uniq -/interfering_jobs filter_uniq // undup_uniq.
                by move: INnth INnth0 => /eqP INnth /eqP INnth0; rewrite INnth INnth0.  
            }
            by rewrite subh3 // addnC; move: INnth => /eqP INnth; rewrite -INnth.
          }
        }

        (* Prove that n_k is at least the number of jobs - 1 *)
        assert (NK: n_k >= n.+1).
        {
          rewrite leqNgt; apply/negP; unfold not; intro LTnk.
          unfold n_k, max_jobs_NC in LTnk.
          rewrite ltn_divLR in LTnk; last by done.
          apply (leq_trans LTnk) in DIST.
          move: INlst1 => /negP BUG; apply BUG.
          unfold service_during; rewrite sum_service_before_arrival; try (by ins). 
          unfold t2. apply leq_trans with (n := job_arrival j_fst + delta);
            first by rewrite leq_add2r.
          rewrite -(ltn_add2l (job_arrival j_fst)) addnBA // in DIST.
          rewrite [_ + _ j_lst]addnC -addnBA // subnn addn0 in DIST.
          by apply ltnW. 
        }
         
        (* If n_k = num_jobs - 1, then we just need to prove that the
           extra term with min() suffices to bound the workload. *)
        move: NK; rewrite leq_eqVlt orbC; move => /orP NK; des;
          first by rewrite ltnS leqNgt NK in NUM.
        {
          move: NK => /eqP NK; rewrite -NK.
          rewrite -addnA addnC; apply leq_add.
          rewrite mulSn; apply leq_add.
          {
            apply leq_trans with (n := job_cost (nth elem sorted_jobs 0));
              first by apply service_interval_le_cost.
            by rewrite -FSTtask; have PROP := job_properties (nth elem sorted_jobs 0); des.
          }
          {
            rewrite mulnC -{2}[n]subn0 -[_*_]addn0 -iter_addn -big_const_nat.
            rewrite big_nat_cond [\sum_(_ <= _ < _ | true)_]big_nat_cond.
            apply leq_sum; intros i; rewrite andbT; move => /andP [_ LE].
            apply leq_trans with (n := job_cost (nth elem sorted_jobs i.+1));
              first by apply service_interval_le_cost.
            assert (TASKnth: job_task (nth elem sorted_jobs i.+1) = tsk).
            {
              exploit (mem_nth elem); last intros IN.
              instantiate (1:= sorted_jobs); instantiate (1 := i.+1);
                by rewrite SIZE ltnS ltnW //.
              move: IN; rewrite -INboth mem_filter.
              by move => /andP [/andP [IN _] _]; apply/eqP.
            }
            by rewrite -TASKnth; have PROP := job_properties (nth elem sorted_jobs i.+1); des.
          }
          rewrite leq_min; apply/andP; split; last first.
          {
            move: INlst => /eqP INlst; rewrite -INlst.
            apply leq_trans with (n := job_cost j_lst);
              first by apply service_interval_le_cost.
            by have PROP := job_properties j_lst; des.
          }
          {
            unfold service_during.
            rewrite -> big_cat_nat with (n := job_arrival j_lst); simpl;
              try (by ins); last by apply ltnW.            
            rewrite sum_service_before_arrival ?leqnn // add0n.
            apply leq_trans with (n := \sum_(job_arrival j_lst <= i < t2) 1).
            apply leq_sum; first by ins; apply service_at_le_max_rate.
            rewrite big_const_nat iter_addn mul1n addn0.
            rewrite -(leq_add2r (job_arrival j_lst)).
            rewrite [t2 - _ + _]subh1; last by apply ltnW.
            unfold t2; rewrite -addnBA // subnn addn0.
            apply leq_trans with (n := job_arrival j_fst + delta);
              first by rewrite leq_add2r.
            rewrite -leq_subLR -addnBA;
              last by rewrite -subndiv_eq_mod leq_subLR leq_addl.
            rewrite -subndiv_eq_mod.
            rewrite subnBA; last by apply leq_trunc_div.
            rewrite [delta + _]addnC -addnBA // subnn addn0.
            rewrite -(leq_add2r (job_arrival j_fst)) in DIST.
            rewrite subh1 in DIST; last by apply BEFOREarr.
            rewrite -addnBA // subnn addn0 addnC NK in DIST.
            by unfold n_k, max_jobs_NC, div_floor in DIST.
          }
        }
     Qed.

   End GuanNoCarry.

   Section GuanCarry.

      Let is_carry_in_job := carried_in job_cost rate sched.
      Let is_idle_at := is_idle sched.

      (* Assume task precedence constraints. *)
      Hypothesis H_task_precedence :
        forall (j j': JobIn arr_seq) t,
          job_task j = job_task j' ->
          job_arrival j < job_arrival j' ->
          scheduled sched j' t ->
          completed job_cost rate sched j t.

      (* Assume that task tsk has a carry-in job in the interval. *)
      Hypothesis H_has_carry_in:
        exists (j: JobIn arr_seq),
          job_task j = tsk /\ is_carry_in_job j t1.

      Hypothesis H_one_processor_idle :
        t1 = 0 \/ exists cpu, is_idle_at cpu (t1 - 1). (*FIX*)

      Let workload_bound := W_CI task_cost task_period.

      (* Then, according to Guan et al.'s schedulability analysis,
         the workload of tsk is bounded by W_CI. *)
      Theorem workload_bounded_by_W_CI :
        workload_of tsk t1 (t1 + delta) <= workload_bound tsk R_tsk delta.
      Proof.
        rename H_jobs_have_valid_parameters into job_properties,
               H_no_deadline_misses_during_interval into no_dl_misses,
               H_valid_task_parameters into task_properties,
               H_completed_jobs_dont_execute into COMP,
               H_task_precedence into PREC.
        unfold valid_sporadic_job, valid_realtime_job, restricted_deadline_model,
               valid_sporadic_taskset, is_valid_sporadic_task, sporadic_task_model,
               workload_of, no_deadline_misses_by,
               workload_bound, W_CI in *; ins; des.

        (* Simplify names *)
        set t2 := t1 + delta.
        set n_k := max_jobs_CI task_cost task_period tsk delta.

        (* Use the definition of workload based on list of jobs. *)
        rewrite workload_eq_workload_joblist; unfold workload_joblist.
        
        (* Identify the subset of jobs that actually cause interference *)
        rewrite -big_filter.
        
        set interfering_jobs :=
          filter (fun (x: JobIn arr_seq) => (job_task x == tsk))
                 (jobs_scheduled_between sched t1 t2).


        (* Remove the elements that we don't care about from the sum *)
        (*assert (SIMPL:
          \sum_(i <- jobs_scheduled_between sched t1 t2 | job_task i == tsk)
             service_during rate sched i t1 t2 =
          \sum_(i <- interfering_jobs) service_during rate sched i t1 t2).
        {
          unfold interfering_jobs.
          rewrite (bigID (fun x => service_during rate sched x t1 t2 == 0)) /=.
          rewrite (eq_bigr (fun x => 0)); last by move => j_i /andP JOBi; des; apply /eqP.
          rewrite big_const_seq iter_addn mul0n add0n add0n.
          by rewrite big_filter.
        } rewrite SIMPL; clear SIMPL.*)

        (* Remember that for any job of tsk, service <= task_cost tsk *)
        assert (LTserv: forall j_i (INi: j_i \in interfering_jobs),
                          service_during rate sched j_i t1 t2 <= task_cost tsk).
        {
          intros j_i; rewrite mem_filter; move => /andP [JOBi _].
          have PROP := job_properties j_i; des.
          move: JOBi => /eqP JOBi; rewrite -JOBi.
          apply leq_trans with (n := job_cost j_i); last by ins. 
          by apply service_interval_le_cost.
        }

        (* Order the sequence of interfering jobs by arrival time, so that
           we can identify the first and last jobs. *)
        set order := fun (x y: JobIn arr_seq) => job_arrival x <= job_arrival y.
        set sorted_jobs := (sort order interfering_jobs).
        assert (SORT: sorted order sorted_jobs);
          first by apply sort_sorted; unfold total, order; ins; apply leq_total.
        rewrite (eq_big_perm sorted_jobs) /=; last by rewrite -(perm_sort order).
   
        (* Remember that both sequences have the same set of elements *)
        assert (INboth: forall x, (x \in interfering_jobs) = (x \in sorted_jobs)).
          by apply perm_eq_mem; rewrite -(perm_sort order).
          
        (* Find some dummy element to use in the nth function *)
        destruct (size sorted_jobs == 0) eqn:SIZE0;
          first by move: SIZE0 =>/eqP SIZE0; rewrite (size0nil SIZE0) big_nil.
        apply negbT in SIZE0; rewrite -lt0n in SIZE0.
        assert (EX: exists elem: JobIn arr_seq, True); des.
          destruct sorted_jobs; [by rewrite ltn0 in SIZE0 | by exists s].
        clear EX SIZE0.

        (* Remember that the jobs are ordered by arrival. *)
        assert (ALL: forall i (LTsort: i < (size sorted_jobs).-1),
                       order (nth elem sorted_jobs i) (nth elem sorted_jobs i.+1)).
        by destruct sorted_jobs; [by ins| by apply/pathP; apply SORT].
        
        (* Now we start the proof. First, we show that the workload bound
           holds if n_k is no larger than the number of interferings jobs. *)
        destruct (size sorted_jobs <= n_k.+1) eqn:NUM.
        {
          rewrite -[\sum_(_ <- _ | _) _]addn0 leq_add // addnC -mulSn.
          apply leq_trans with (n := \sum_(x <- sorted_jobs) task_cost tsk);
            last by rewrite big_const_seq iter_addn addn0 mulnC leq_mul2r; apply/orP; right.
          {
            rewrite [\sum_(_ <- _) service_during _ _ _ _ _]big_seq_cond.
            rewrite [\sum_(_ <- _) task_cost _]big_seq_cond.
            by apply leq_sum; intros j_i; move/andP => xxx; des; apply LTserv; rewrite INboth.
          }
        }
        apply negbT in NUM; rewrite -ltnNge in NUM.

        (* Now we index the sum to access the first and last elements. *)
        rewrite (big_nth elem).

        (* First and last only exist if there are at least 2 jobs. Thus, we must show
           that the bound holds for the empty list. *)
        destruct (size sorted_jobs) eqn:SIZE; first by rewrite big_geq.
        rewrite SIZE.
        
        (* Let's derive some properties about the first element. *)
        exploit (mem_nth elem); last intros FST.
          by instantiate (1:= sorted_jobs); instantiate (1 := 0); rewrite SIZE.


        move: FST (FST) => FSTin; rewrite -INboth mem_filter (scheduled_between_implies_service rate);
          last by admit.  
        move => /andP [FSTtsk FSTserv].  

        (* Now we show that the bound holds for a singleton set of interfering jobs. *)
        destruct n.
        {
          destruct n_k eqn:EQnk;
            [by rewrite mul0n add0n big_nat_recl // | by done].
        } rewrite [nth]lock /= -lock in ALL.
        
        (*    unfold n_k, max_jobs_NC, div_floor in EQnk.
            rewrite -subndiv_eq_mod EQnk mul0n subn0.
            rewrite leq_min; apply/andP; split; last first.
            {
              apply leq_trans with (n := job_cost (nth elem sorted_jobs 0));
                first by apply service_interval_le_cost.
              by rewrite -FSTtask; have PROP := job_properties (nth elem sorted_jobs 0); des.
            }
            {
              apply leq_trans with (n := \sum_(t1 <= t < t2) 1).
                by apply leq_sum; ins; apply service_at_le_max_rate.
                by unfold t2; rewrite big_const_nat iter_addn mul1n addn0 addnC -addnBA// subnn addn0.
            }
          }
        } rewrite [nth]lock /= -lock in ALL.*)
    
        (* Knowing that we have at least two elements, we take first and last out of the sum *) 
        rewrite [nth]lock big_nat_recl // big_nat_recr // /= -lock.
        rewrite addnA addnC addnA.
        set j_fst := (nth elem sorted_jobs 0).
        set j_lst := (nth elem sorted_jobs n.+1).
                       
        (* Now we infer some facts about how first and last are ordered in the timeline *)
        assert (LST: j_lst \in interfering_jobs).
        {
            by unfold j_lst; rewrite INboth; apply mem_nth; rewrite SIZE.
        }
        move: LST (LST) => LSTin.
        rewrite mem_filter (scheduled_between_implies_service rate);
          last by admit. (* RATE bug *)

        move => /andP [LSTtsk LSTserv].
        
        assert (AFTERt1: t1 <= job_arrival j_fst + R_tsk).
        {
          rewrite leqNgt; apply /negP; unfold not; intro LTt1.
          move: FSTserv => /eqP FSTserv; apply FSTserv.
          apply (sum_service_after_job_rt_zero job_cost) with (R := R_tsk);
            try (by ins); last by apply ltnW.
          apply H_response_time_bound; first by apply/eqP.
          by apply leq_trans with (n := t1); last by apply leq_addr.
        }

        (*assert (AFTERt1: t1 <= job_arrival j_fst).
        {
          rewrite leqNgt; apply /negP; unfold not; intro LTt1.
          apply H_no_carry_in; exists j_fst; split; first by apply/eqP.
          unfold is_carry_in_job, carried_in; apply/andP; split; first by done.
          unfold completed_jobs_dont_execute, completed in *.
          apply/negP; intro COMPLETED.
          specialize (COMP j_fst t2); rewrite leqNgt in COMP.
          move: COMP => /negP COMP; apply COMP.
          unfold service; rewrite -> big_cat_nat with (n := t1);
            [simpl | by done | by apply leq_addr].
          move: COMPLETED => /eqP COMPLETED; rewrite -COMPLETED.
          apply leq_trans with (n := service rate sched j_fst t1 + 1);
            first by rewrite addn1.
          by rewrite leq_add2l lt0n.
        }*)

        (*assert (AFTERt1': t1 <= job_arrival j_lst).
        {
          rewrite leqNgt; apply /negP; unfold not; intro LTt1.
          apply H_no_carry_in; exists j_lst; split; first by apply/eqP.
          unfold is_carry_in_job, carried_in; apply/andP; split; first by done.
          unfold completed_jobs_dont_execute, completed in *.
          apply/negP; intro COMPLETED.
          specialize (COMP j_lst t2); rewrite leqNgt in COMP.
          move: COMP => /negP COMP; apply COMP.
          unfold service; rewrite -> big_cat_nat with (n := t1);
            [simpl | by done | by apply leq_addr].
          move: COMPLETED => /eqP COMPLETED; rewrite -COMPLETED.
          apply leq_trans with (n := service rate sched j_lst t1 + 1);
            first by rewrite addn1.
          by rewrite leq_add2l lt0n.
        }*)

        assert (BEFOREt2: job_arrival j_lst < t2).
        {
          rewrite leqNgt; apply/negP; unfold not; intro LT2.
          move: LSTserv => /eqP LSTserv; apply LSTserv. 
          by unfold service_during; rewrite sum_service_before_arrival.
        }

        assert (BEFOREarr: job_arrival j_fst <= job_arrival j_lst).
        {
          unfold j_fst, j_lst; rewrite -[n.+1]add0n.
          apply prev_le_next; last by rewrite add0n SIZE leqnn.
          by unfold order in ALL; intro i; rewrite SIZE; apply ALL.
        }
        
        (* Now we upper-bound the service of the middle jobs. *)
        assert (BOUNDmid: \sum_(0 <= i < n)
                           service_during rate sched (nth elem sorted_jobs i.+1) t1 t2 <=
                             n * task_cost tsk).
        {
          apply leq_trans with (n := n * task_cost tsk);
            last by rewrite leq_mul2l; apply/orP; right. 
          apply leq_trans with (n := \sum_(0 <= i < n) task_cost tsk);
            last by rewrite big_const_nat iter_addn addn0 mulnC subn0.
          rewrite big_nat_cond [\sum_(0 <= i < n) task_cost _]big_nat_cond.
          apply leq_sum; intros i; rewrite andbT; move => /andP LT; des.
          by apply LTserv; rewrite INboth mem_nth // SIZE ltnS leqW.
        }

        (* Conclude that the distance between first and last is at least n + 1 periods,
           where n is the number of middle jobs. *)
        assert (DIST: job_arrival j_lst - job_arrival j_fst >= n.+1 * (task_period tsk)).
        {
          assert (EQnk: n.+1=(size sorted_jobs).-1); first by rewrite SIZE. 
          unfold j_fst, j_lst; rewrite EQnk telescoping_sum; last by rewrite SIZE.
          rewrite -[_ * _ tsk]addn0 mulnC -iter_addn -{1}[_.-1]subn0 -big_const_nat. 
          rewrite big_nat_cond [\sum_(0 <= i < _)(_-_)]big_nat_cond.
          apply leq_sum; intros i; rewrite andbT; move => /andP LT; des.
          {
            (* To simplify, call the jobs 'cur' and 'next' *)
            set cur := nth elem sorted_jobs i.
            set next := nth elem sorted_jobs i.+1.
            clear BOUNDmid LT LTserv j_fst j_lst
                  FSTin FSTserv FSTtsk LSTin LSTserv LSTtsk
                  BEFOREarr AFTERt1 BEFOREt2.

            (* Show that cur arrives earlier than next *)
            assert (ARRle: job_arrival cur <= job_arrival next).
            {
              unfold cur, next; rewrite -addn1; apply prev_le_next; first by rewrite SIZE.
              by apply leq_trans with (n := i.+1); try rewrite addn1.
            }
             
            (* Show that both cur and next are in the arrival sequence *)
            assert (INnth: cur \in interfering_jobs /\
                           next \in interfering_jobs).
              rewrite 2!INboth; split.
              by apply mem_nth, (ltn_trans LT0); destruct sorted_jobs; ins.
              by apply mem_nth; destruct sorted_jobs; ins.
            rewrite 2?mem_filter in INnth; des.

            (* Use the sporadic task model to conclude that cur and next are separated
               by at least (task_period tsk) units. Of course this only holds if cur != next.
               Since we don't know much about the list (except that it's sorted), we must
               also prove that it doesn't contain duplicates. *)
            assert (CUR_LE_NEXT: job_arrival cur + task_period (job_task cur) <= job_arrival next).
            {
              apply H_sporadic_tasks; last by ins.
              unfold cur, next, not; intro EQ; move: EQ => /eqP EQ.
              rewrite nth_uniq in EQ; first by move: EQ => /eqP EQ; intuition.
                by apply ltn_trans with (n := (size sorted_jobs).-1); destruct sorted_jobs; ins.
                by destruct sorted_jobs; ins.
                by rewrite sort_uniq -/interfering_jobs filter_uniq // undup_uniq.
                by move: INnth INnth0 => /eqP INnth /eqP INnth0; rewrite INnth INnth0.  
            }
            by rewrite subh3 // addnC; move: INnth => /eqP INnth; rewrite -INnth.
          }
        }

        (* Prove that n_k is at least the number of jobs - 1 *)
        assert (NK: n_k >= n).
        {
          rewrite leqNgt; apply/negP; unfold not; intro LTnk.
          unfold n_k, max_jobs_NC in LTnk.
          (*rewrite ltn_divLR in LTnk; last by done.
          apply (leq_trans LTnk) in DIST.
          move: LSTserv => /negP BUG; apply BUG.
          unfold service_during; rewrite sum_service_before_arrival; try (by ins). 
          unfold t2. apply leq_trans with (n := job_arrival j_fst + delta);
            first by rewrite leq_add2r.
          rewrite -(ltn_add2l (job_arrival j_fst)) addnBA // in DIST.
          rewrite [_ + _ j_lst]addnC -addnBA // subnn addn0 in DIST.
          by apply ltnW.*)
          admit.
        }

        (* With the facts that we derived, we can now prove the workload bound.  
           There are two cases to be analyze since n <= n_k < n + 2, where n is the number
           of middle jobs. *)
        rewrite ltnS ltnS in NUM.
        assert (EQnk: n_k = n); last clear NK NUM.
          by apply/eqP; rewrite eqn_leq; apply/andP; split.
        rewrite EQnk addnC -addnA; apply leq_add.
        {
          apply leq_trans with (n := \sum_(0 <= i < n) task_cost tsk). 
          rewrite big_nat_cond [\sum_(_ <= _ < _ | true) _]big_nat_cond.
          apply leq_sum; intro i; rewrite andbT; move => /andP [_ LTi];
            first by apply LTserv; rewrite INboth mem_nth // SIZE 2!ltnS ltnW.
          by rewrite big_const_nat iter_addn subn0 addn0 mulnC.
        }
        apply leq_add; first by apply LTserv.
        assert (CARRY: is_carry_in_job j_fst t1).
        {
          (* By contradiction. Suppose j_fst is not the carried-in job. *)
          rewrite -[is_carry_in_job _ _]negbK; apply/negP; intro NOTCARRY.
          destruct H_has_carry_in as [j_in [JOBin CARRY]].
          destruct (j_fst == j_in) eqn:EQ; move: EQ => /eqP EQ;
            first by rewrite EQ CARRY in NOTCARRY.
          move: CARRY => /andP [ARRin NOTCOMPin].
          unfold arrived_before in ARRin.
          move: H_sporadic_tasks FSTtsk => SPO /eqP FSTtsk.
          unfold is_carry_in_job, carried_in in NOTCARRY.
          destruct (job_arrival j_fst <= job_arrival j_in) eqn:LEQ.
          {
            (* If j_fst arrives before j_in, then j_fst is also a carry-in job. Contradiction! *)
            apply leq_ltn_trans with (p := t1) in LEQ; last by done.
            move: NOTCARRY => /negP NOTCARRY; apply NOTCARRY; clear NOTCARRY.
            apply/andP; split; first by done.
            unfold completed; apply/negP; move => /eqP EQcost.
            move: FSTserv => /negP FSTserv; apply FSTserv.
            rewrite -leqn0 -(leq_add2l (service rate sched j_fst t1)); rewrite addn0.
            rewrite {2}[service _ _ _ _]EQcost.
            by unfold service, service_during; rewrite <- big_cat_nat with (n := t1);
              [by apply COMP | by done | by apply leq_addr].
          }
          {
            (* If j_in arrives before f_fst, then j_in must have been scheduled on the interval,
               otherwise it's not a carry-in job. *)
            apply negbT in LEQ; rewrite -ltnNge in LEQ.
            assert (LISTin: j_in \in sorted_jobs).
            {
              destruct (service_during rate sched j_in t1 t2 != 0) eqn:SERV.
              {
                (* If j_in executes in the interval, then it automatically belongs to sorted_jobs.*)
                rewrite -INboth mem_filter JOBin eq_refl andTb.
                by rewrite (scheduled_between_implies_service rate);
                  last by admit.
              }
              {
                (* Else, there must be a time when j_fst executes while j_in does not.
                   This violates task precedence constraints. *)
                apply job_scheduled_during_interval in FSTserv.
                destruct FSTserv as [t [LT' FSTserv]]; move: LT' => /andP [LEt GTt].
                
                exploit (PREC j_in j_fst t);
                  [by rewrite FSTtsk JOBin | by apply LEQ | | intro COMPin].
                {
                  rewrite -[scheduled _ _ _]negbK; apply/negP; intro BUG.
                  apply not_scheduled_no_service with (rate0 := rate) in BUG.                 by rewrite BUG in FSTserv.
                }
                clear PREC SPO EQ.
                apply negbT in SERV; rewrite negbK in SERV.
                unfold completed, service, service_during in NOTCOMPin, COMPin, SERV.
                assert (BUG: \sum_(0 <= t0 < t) service_at rate sched j_in t0 < job_cost j_in).
                {
                  rewrite -> big_cat_nat with (n := t1);
                    [simpl |  by done | by apply LEt].
                  assert (TMP: \sum_(0 <= t0 < t1) service_at rate sched j_in t0 < job_cost j_in).
                  {
                    rewrite ltn_neqAle; apply/andP; split; first by done.
                    by apply COMP.
                  }
                  rewrite addnC -addn1 -[job_cost _]addn0 -addnA addnC.
                  apply leq_add; first by rewrite addn1.
                  apply leq_trans with (n := \sum_(t1 <= i < t) service_at rate sched j_in i + \sum_(t <= i < t2) service_at rate sched j_in i);
                    first by apply leq_addr.
                  by rewrite <- big_cat_nat;
                    [by rewrite leqn0 | by apply LEt | by apply ltnW, GTt].
                }
                by move: COMPin => /eqP COMPin; rewrite COMPin ltnn in BUG.
              }
            }   
            move: LISTin => /nthP LISTin; destruct (LISTin elem) as [i LTi EQi].
            assert (BUG: ~~ (job_arrival j_fst > job_arrival j_in)).
            {
              rewrite -leqNgt -EQi -[i]add0n; apply prev_le_next; destruct sorted_jobs; try (by done).
              intros j LTj; apply ALL; simpl in *.
              move: SIZE; move/eqP; rewrite -addn1 -[n.+2]addn1 eqn_add2r; move => /eqP SIZE.
              by rewrite SIZE in LTj.
            }
            by rewrite LEQ in BUG.
          }
        }

        (* Now that we know j_fst is the carried-in job, we can know that
           it's cost is limited to (task_cost tsk - 1). *)
        admit.
      Qed.

   End GuanCarry.
   
  End ProofWorkloadBound.


End WorkloadBoundGuan.






  