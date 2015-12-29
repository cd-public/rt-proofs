Require Import workload Vbase job task schedule task_arrival response_time
               schedulability util_divround util_lemmas
               ssreflect ssrbool eqtype ssrnat seq div fintype bigop path.

Module WorkloadBoundFP.
 Import Job SporadicTaskset Schedule SporadicTaskArrival ResponseTime Schedulability Workload.
  Section WorkloadBound.

    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> nat.
    Variable task_period: sporadic_task -> nat.
    
    Variable tsk: sporadic_task.
    Variable R_tsk: time. (* Known response-time bound for the task *)
    Variable delta: time. (* Length of the interval *)
    
    (* Bound on the number of jobs that execute completely in the interval *)
    Definition max_jobs :=
      div_floor (delta + R_tsk - task_cost tsk) (task_period tsk).

    (* Bertogna and Cirinei's bound on the workload of a task in an interval of length delta *)
    Definition W :=
      let e_k := (task_cost tsk) in
      let p_k := (task_period tsk) in            
        minn e_k (delta + R_tsk - e_k - max_jobs * p_k) + max_jobs * e_k.

  End WorkloadBound.
  
  Section BasicLemmas.

    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> nat.
    Variable task_period: sporadic_task -> nat.

    (* Let tsk be any task...*)
    Variable tsk: sporadic_task.

    (* ...with period > 0. *)
    Hypothesis H_period_positive: task_period tsk > 0.

    (* Let R1 <= R2 be two response-time bounds that
       are larger than the cost of the tsk. *)
    Variable R1 R2: time.
    Hypothesis H_R_lower_bound: R1 >= task_cost tsk.
    Hypothesis H_R1_le_R2: R1 <= R2.
      
    Let workload_bound := W task_cost task_period tsk.

    (* Then, Bertogna and Cirinei's workload bound is monotonically increasing. *) 
    Lemma W_monotonic :
      forall t1 t2,
        t1 <= t2 ->
        workload_bound R1 t1 <= workload_bound R2 t2.
    Proof.
      intros t1 t2 LEt.
      unfold workload_bound, W, max_jobs, div_floor; rewrite 2!subndiv_eq_mod.
      set e := task_cost tsk; set p := task_period tsk.
      set x1 := t1 + R1.
      set x2 := t2 + R2.
      set delta := x2 - x1.
      rewrite -[x2](addKn x1) -addnBA; fold delta;
        last by apply leq_add.
      
      induction delta; first by rewrite addn0 leqnn.
      {
         apply (leq_trans IHdelta).

         (* Prove special case for p <= 1. *)
         destruct (leqP p 1) as [LTp | GTp].
         {
           rewrite leq_eqVlt in LTp; move: LTp => /orP LTp; des;
             last by rewrite ltnS in LTp; apply (leq_trans H_period_positive) in LTp. 
           {
             move: LTp => /eqP LTp; rewrite LTp 2!modn1 2!divn1.
             rewrite leq_add2l leq_mul2r; apply/orP; right.
             by rewrite leq_sub2r // leq_add2l.
           }
         }
         (* Harder case: p > 1. *)
         {
           assert (EQ: (x1 + delta.+1 - e) = (x1 + delta - e).+1).
           {
             rewrite -[(x1 + delta - e).+1]addn1.
             rewrite [_+1]addnC addnBA; last first.
             {
               apply (leq_trans H_R_lower_bound).
               by rewrite -addnA addnC -addnA leq_addr.
             }
             by rewrite [1 + _]addnC -addnA addn1.
           } rewrite -> EQ in *; clear EQ.
         
         have DIV := divSn_cases (x1 + delta - e) p GTp; des.
         {
           rewrite DIV leq_add2r leq_min; apply/andP; split;
             first by rewrite geq_minl.
           by apply leq_trans with (n := (x1 + delta - e) %% p);
             [by rewrite geq_minr | by rewrite -DIV0 addn1 leqnSn].
         }
         {
           rewrite -[minn e _]add0n -addnA; apply leq_add; first by ins.
           rewrite -DIV mulnDl mul1n [_ + e]addnC.
           by apply leq_add; [by rewrite geq_minl | by ins].
         }
       }
     }
   Qed.

  End BasicLemmas.
 
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
    
    Section BertognaCirinei.
      
    (* Then the workload of the task in the interval is bounded by W. *)
      Let workload_bound := W task_cost task_period.
    
      Theorem workload_bounded_by_W :
        workload_of tsk t1 (t1 + delta) <= workload_bound tsk R_tsk delta.
      Proof.
        rename H_jobs_have_valid_parameters into job_properties,
               H_no_deadline_misses_during_interval into no_dl_misses,
               H_valid_task_parameters into task_properties.
        unfold valid_sporadic_job, valid_realtime_job, restricted_deadline_model,
               valid_sporadic_taskset, is_valid_sporadic_task, sporadic_task_model,
               workload_of, no_deadline_misses_by, workload_bound, W in *; ins; des.

        (* Simplify names *)
        set t2 := t1 + delta.
        set n_k := max_jobs task_cost task_period tsk R_tsk delta.

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
          rewrite -[\sum_(_ <- _ | _) _]add0n leq_add //.
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
          destruct n_k; last by ins.
          {
            rewrite 2!mul0n addn0 subn0 big_nat_recl // big_geq // addn0.
            rewrite leq_min; apply/andP; split.
            {
              apply leq_trans with (n := job_cost (nth elem sorted_jobs 0));
                first by apply service_interval_le_cost.
              by rewrite -FSTtask; have PROP := job_properties (nth elem sorted_jobs 0); des.
            }
            {
              rewrite -addnBA; last by ins.
              rewrite -[service_during _ _ _ _ _]addn0.
              apply leq_add; last by ins.
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

        assert (AFTERt1: t1 <= job_arrival j_fst + R_tsk).
        {
          rewrite leqNgt; apply /negP; unfold not; intro LTt1.
          move: INfst1 => /eqP INfst1; apply INfst1.
          apply (sum_service_after_job_rt_zero job_cost) with (R := R_tsk);
            try (by done); last by apply ltnW.
          apply H_response_time_bound; first by apply/eqP.
          by apply leq_trans with (n := t1); last by apply leq_addr.
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

        (* Next, we upper-bound the service of the first and last jobs using their arrival times. *)
        assert (BOUNDend: service_during rate sched j_fst t1 t2 +
                          service_during rate sched j_lst t1 t2 <=
                          (job_arrival j_fst  + R_tsk - t1) + (t2 - job_arrival j_lst)).
        {
          apply leq_add; unfold service_during.
          {
            rewrite -[_ + _ - _]mul1n -[1*_]addn0 -iter_addn -big_const_nat.
            apply leq_trans with (n := \sum_(t1 <= t < job_arrival j_fst + R_tsk)
                                           service_at rate sched j_fst t);
              last by apply leq_sum; ins; apply service_at_le_max_rate.
            destruct (job_arrival j_fst + R_tsk < t2) eqn:LEt2; last first.
            {
              unfold t2; apply negbT in LEt2; rewrite -ltnNge in LEt2.
              rewrite -> big_cat_nat with (n := t1 + delta) (p := job_arrival j_fst + R_tsk);
                [by apply leq_addr | by apply leq_addr | by done].
            }
            {
              rewrite -> big_cat_nat with (n := job_arrival j_fst + R_tsk); [| by ins|by apply ltnW].
              rewrite -{2}[\sum_(_ <= _ < _) _]addn0 /=.
              rewrite leq_add2l leqn0; apply/eqP.
              apply (sum_service_after_job_rt_zero job_cost) with (R := R_tsk);
                try (by done); last by apply leqnn.
              by apply H_response_time_bound; first by apply/eqP.
            }
          }
          {
            rewrite -[_ - _]mul1n -[1 * _]addn0 -iter_addn -big_const_nat.
            destruct (job_arrival j_lst <= t1) eqn:LT.
            {
              apply leq_trans with (n := \sum_(job_arrival j_lst <= t < t2)
                                          service_at rate sched j_lst t);
                first by rewrite -> big_cat_nat with (m := job_arrival j_lst) (n := t1);
                  [by apply leq_addl | by ins | by apply leq_addr].
              by apply leq_sum; ins; apply service_at_le_max_rate.
            }
            {
              apply negbT in LT; rewrite -ltnNge in LT.
              rewrite -> big_cat_nat with (n := job_arrival j_lst); [|by apply ltnW| by apply ltnW].
              rewrite /= -[\sum_(_ <= _ < _) 1]add0n; apply leq_add.
              rewrite sum_service_before_arrival; [by apply leqnn | by ins | by apply leqnn].
              by apply leq_sum; ins; apply service_at_le_max_rate.
            }
          }
        }

        (* Let's simplify the expression of the bound *)
        assert (SUBST: job_arrival j_fst + R_tsk - t1 + (t2 - job_arrival j_lst) =
                       delta + R_tsk - (job_arrival j_lst - job_arrival j_fst)).
        {
          rewrite addnBA; last by apply ltnW.
          rewrite subh1 // -addnBA; last by apply leq_addr.
          rewrite addnC [job_arrival _ + _]addnC.
          unfold t2; rewrite [t1 + _]addnC -[delta + t1 - _]subnBA // subnn subn0.
          rewrite addnA -subnBA; first by ins.
          {
            unfold j_fst, j_lst; rewrite -[n.+1]add0n.
            by apply prev_le_next; [by rewrite SIZE | by rewrite SIZE add0n ltnSn].
          }
        } rewrite SUBST in BOUNDend; clear SUBST.

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
            clear BOUNDend BOUNDmid LT LTserv j_fst j_lst
                  INfst INfst0 INfst1 AFTERt1 BEFOREt2 FSTserv FSTtask FSTin.

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

        (* Prove that n_k is at least the number of the middle jobs *)
        assert (NK: n_k >= n).
        {
          rewrite leqNgt; apply/negP; unfold not; intro LTnk.
          assert (DISTmax: job_arrival j_lst - job_arrival j_fst >= delta + task_period tsk).
          {
            apply leq_trans with (n := n_k.+2 * task_period tsk).
            {
              rewrite -addn1 mulnDl mul1n leq_add2r.
              apply leq_trans with (n := delta + R_tsk - task_cost tsk);
                first by rewrite -addnBA //; apply leq_addr.
              by apply ltnW, ltn_ceil, task_properties0.
            }
            by apply leq_trans with (n.+1 * task_period tsk); 
              [by rewrite leq_mul2r; apply/orP; right | by apply DIST].
          }
          rewrite <- leq_add2r with (p := job_arrival j_fst) in DISTmax.
          rewrite addnC subh1 in DISTmax;
            last by unfold j_fst, j_lst; rewrite -[_.+1]add0n prev_le_next // SIZE // add0n ltnS leqnn.
          rewrite -subnBA // subnn subn0 in DISTmax.
          rewrite [delta + task_period tsk]addnC addnA in DISTmax.
          generalize BEFOREt2; move: BEFOREt2; rewrite {1}ltnNge; move => /negP BEFOREt2'.
          intros BEFOREt2; apply BEFOREt2'; clear BEFOREt2'.
          apply leq_trans with (n := job_arrival j_fst + task_deadline tsk + delta);
            last by apply leq_trans with (n := job_arrival j_fst + task_period tsk + delta);
              [rewrite leq_add2r leq_add2l; apply H_restricted_deadline | apply DISTmax].
          {
            (* Show that j_fst doesn't execute d_k units after its arrival. *)
            unfold t2; rewrite leq_add2r; rename H_completed_jobs_dont_execute into EXEC.
            unfold task_misses_no_deadline_before, job_misses_no_deadline, completed in *; des.
            exploit (no_dl_misses j_fst INfst); last intros COMP.
            { 
              (* Prove that arr_fst + d_k <= t2 *)
              apply leq_ltn_trans with (n := job_arrival j_lst); last by done.
              apply leq_trans with (n := job_arrival j_fst + task_period tsk + delta); last by ins.
              rewrite -addnA leq_add2l -[job_deadline _]addn0.
              apply leq_add; last by ins.
              specialize (job_properties j_fst); des.
              by rewrite job_properties1 FSTtask H_restricted_deadline.
            }
            rewrite leqNgt; apply/negP; unfold not; intro LTt1.
            (* Now we assume that (job_arrival j_fst + d_k < t1) and reach a contradiction.
               Since j_fst doesn't miss deadlines, then the service it receives between t1 and t2
               equals 0, which contradicts the previous assumption that j_fst interferes in
               the scheduling window. *)
            clear BEFOREt2 DISTmax LTnk DIST BOUNDend BOUNDmid FSTin; move: EXEC => EXEC.
            move: INfst1 => /eqP SERVnonzero; apply SERVnonzero.
            {
              unfold service_during; apply/eqP; rewrite -leqn0.
              rewrite <- leq_add2l with (p := job_cost j_fst); rewrite addn0.
              move: COMP => /eqP COMP; unfold service in COMP; rewrite -{1}COMP.
              apply leq_trans with (n := service rate sched j_fst t2); last by apply EXEC.
              unfold service; rewrite -> big_cat_nat with (m := 0) (p := t2) (n := t1);
                [rewrite leq_add2r /= | by ins | by apply leq_addr].
              rewrite -> big_cat_nat with (p := t1) (n := job_arrival j_fst + job_deadline j_fst);
                 [| by ins | by apply ltnW; specialize (job_properties j_fst); des;
                             rewrite job_properties1 FSTtask].
              by rewrite /= -{1}[\sum_(_ <= _ < _) _]addn0 leq_add2l.
            }
          }    
        }

        (* With the facts that we derived, we can now prove the workload bound.  
           There are two cases to be analyze since n <= n_k < n + 2, where n is the number
           of middle jobs. *)
        move: NK; rewrite leq_eqVlt orbC leq_eqVlt; move => /orP NK; des.
        move: NK => /orP NK; des; last by rewrite ltnS leqNgt NK in NUM.
        {
          (* Case 1: n_k = n + 1, where n is the number of middle jobs. *)
          move: NK => /eqP NK; rewrite -NK.
          rewrite -{2}addn1 mulnDl mul1n [n* _ + _]addnC addnA addn_minl.
          apply leq_add; [clear BOUNDmid | by apply BOUNDmid].
          rewrite leq_min; apply/andP; split;
            first by apply leq_add; apply LTserv; rewrite INboth mem_nth // SIZE.
          {
            rewrite subnAC subnK; last first.
            {
              assert (TMP: delta + R_tsk = task_cost tsk + (delta + R_tsk - task_cost tsk));
                first by rewrite subnKC; [by ins | by rewrite -[task_cost _]add0n; apply leq_add].
              rewrite TMP; clear TMP.
              rewrite -{1}[task_cost _]addn0 -addnBA NK; [by apply leq_add | by apply leq_trunc_div].
            }
            apply leq_trans with (delta + R_tsk - (job_arrival j_lst - job_arrival j_fst));
              first by rewrite addnC; apply BOUNDend.
            by apply leq_sub2l, DIST.
          }
        }
        {
          (* Case 2: n_k = n, where n is the number of middle jobs. *)
          move: NK => /eqP NK; rewrite -NK.
          apply leq_add; [clear BOUNDmid | by apply BOUNDmid].
          apply leq_trans with (delta + R_tsk - (job_arrival j_lst - job_arrival j_fst));
            first by rewrite addnC; apply BOUNDend.
          rewrite leq_min; apply/andP; split.
          {
            rewrite leq_subLR [_ + task_cost _]addnC -leq_subLR.
            apply leq_trans with (n.+1 * task_period tsk); last by apply DIST.
            rewrite NK ltnW // -ltn_divLR; last by apply task_properties0.
            by unfold n_k, max_jobs, div_floor.
          }
          {
            rewrite -subnDA; apply leq_sub2l.
            apply leq_trans with (n := n.+1 * task_period tsk); last by apply DIST.
            rewrite -addn1 addnC mulnDl mul1n.
            rewrite leq_add2l; last by apply task_properties3.
          }
        }
      Qed.

    End BertognaCirinei.
    
  End ProofWorkloadBound.

End WorkloadBoundFP.
    