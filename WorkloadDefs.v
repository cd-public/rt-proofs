Require Import Vbase JobDefs TaskDefs ScheduleDefs TaskArrivalDefs ResponseTimeDefs
        SchedulabilityDefs divround helper
        ssreflect ssrbool eqtype ssrnat seq div fintype bigop path ssromega.

Module Workload.

  Import Job SporadicTaskset Schedule SporadicTaskArrival ResponseTime Schedulability.
  
  Section WorkloadDef.
    
    Context {Job: eqType}.
    Variable job_task: Job -> sporadic_task.
    
    Variable rate: Job -> processor -> nat.
    Variable num_cpus: nat.
    Variable sched: schedule Job.

    (* Consider some task *)
    Variable tsk: sporadic_task.

    (* First, we define a function that returns the amount of service
       received by this task in a particular processor. *)
    Definition service_of_task (cpu: processor) (j: option Job) : nat :=
      match j with
        | Some j' => (job_task j' == tsk) * (rate j' cpu)
        | None => 0
      end.

    (* Next, workload is defined as the service received by jobs of
       the task in the interval [t1,t2). *)
    Definition workload (t1 t2: time) :=
      \sum_(t1 <= t < t2)
        \sum_(0 <= cpu < num_cpus)
          service_of_task cpu (sched cpu t).

    (* We provide an alternative definition for workload,
       which is more suitable for our proof.
       It requires computing the list of jobs that are scheduled
       between t1 and t2 (without duplicates). *)
    Definition jobs_scheduled_between (t1 t2: time) : list Job :=
      undup (\cat_(t1 <= t < t2)
               \cat_(0 <= cpu < num_cpus)
                 match (sched cpu t) with
                 | Some j => [::j]
                 | None => [::]
                 end).

    (* Now, we define workload by summing up the cumulative service
       during [t1,t2) of the scheduled jobs, but only those spawned
       by the task that we care about. *)
    Definition workload_joblist (t1 t2: time) :=
      \sum_(j <- jobs_scheduled_between t1 t2 | job_task j == tsk)
        service_during num_cpus rate sched j t1 t2.

    (* Next, we show that the two definitions are equivalent. *)
    Lemma workload_eq_workload_joblist (t1 t2: time) :
      workload t1 t2 = workload_joblist t1 t2.
    Proof.
      unfold workload, workload_joblist, service_during.
      rewrite [\sum_(j <- jobs_scheduled_between _ _ | _) _]exchange_big /=.
      rewrite -> eq_big_nat with (F2 := fun j =>
                \sum_(i <- jobs_scheduled_between t1 t2 | job_task i == tsk)
                  service_at num_cpus rate sched i j); first by ins.
      intros t LEt; rewrite exchange_big /=.
      rewrite -> eq_big_nat with (F2 := fun j =>
              \sum_(i0 <- jobs_scheduled_between t1 t2 | job_task i0 == tsk)
                    (sched j t == Some i0) * rate i0 j); first by ins.
      intros cpu LEcpu; rewrite -big_filter.
      destruct (sched cpu t) eqn:SCHED; simpl; last first.
        by rewrite -> eq_bigr with (F2 := fun i => 0);
          [by rewrite big_const_seq iter_addn | by ins].
        {
          rename s into j; destruct (job_task j == tsk) eqn:EQtsk;
            try rewrite mul1n; try rewrite mul0n.
          {  
            rewrite -> bigD1_seq with (j := j); last by rewrite filter_undup undup_uniq.
            { 
              rewrite -> eq_bigr with (F2 := fun i => 0);
                first by rewrite big_const_seq iter_addn /= mul0n 2!addn0 eq_refl mul1n.
                intros i NEQ; destruct (Some j == Some i) eqn:SOMEeq; last by rewrite mul0n.
                by move: SOMEeq => /eqP SOMEeq; inversion SOMEeq; subst; rewrite eq_refl in NEQ.
            }
            {
              rewrite mem_filter; apply/andP; split; first by ins.
              rewrite mem_undup.
              apply mem_bigcat with (j := t); first by ins.
              apply mem_bigcat with (j := cpu); first by ins.
              by rewrite SCHED inE; apply/eqP.
            }
          }
          {
            rewrite big_filter; rewrite -> eq_bigr with (F2 := fun i => 0);
              first by rewrite big_const_seq iter_addn mul0n addn0.
            intros i EQtsk2; destruct (Some j == Some i) eqn:SOMEeq; last by rewrite mul0n.
            by move: SOMEeq => /eqP SOMEeq; inversion SOMEeq;
              subst; rewrite EQtsk2 in EQtsk.
          }
        }
      Qed.
 
  End WorkloadDef.

  Section WorkloadBound.

    Variable tsk: sporadic_task.
    Variable R_tsk: time. (* Known response-time bound for the task *)
    Variable delta: time. (* Length of the interval *)
    
    (* Bound on the number of jobs that execute completely in the interval *)
    Definition max_jobs :=
      div_floor (delta + R_tsk - task_cost tsk) (task_period tsk).

    (* Bertogna and Ciritnei's bound on the workload of a task in an interval of length delta *)
    Definition W :=
      let e_k := (task_cost tsk) in
      let d_k := (task_deadline tsk) in
      let p_k := (task_period tsk) in            
        minn e_k (delta + R_tsk - e_k - max_jobs * p_k) + max_jobs * e_k.

  End WorkloadBound.

  Section ProofWorkloadBound.
  
    Variable Job: eqType.
    Variable job_arrival: Job -> nat.
    Variable job_cost: Job -> nat.
    Variable job_task: Job -> sporadic_task.
    Variable job_deadline: Job -> nat.

    (* Assume that all jobs have valid parameters *)
    Hypothesis jobs_have_valid_parameters :
      forall j, valid_sporadic_task_job job_cost job_deadline job_task j.

    Variable num_cpus: nat.
    Variable rate: Job -> processor -> nat.
    Variable schedule_of_platform: schedule Job -> Prop.

    (* Assume any schedule of a given platform. *)
    Variable sched: schedule Job.
    Hypothesis sched_of_platform: schedule_of_platform sched.

    (* Assumption: jobs only execute if they arrived.
       This is used to eliminate jobs that arrive after end of the interval t1 + delta. *)
    Hypothesis jobs_must_arrive:
      job_must_arrive_to_exec job_arrival num_cpus sched.

    (* Assumption: jobs do not execute after they completed.
       This is used to eliminate jobs that complete before the start of the interval t1. *)
    Hypothesis completed_jobs:
      completed_job_doesnt_exec job_cost num_cpus rate sched.

    (* Assumptions:
         1) A job does not execute in parallel.
         2) The service rate of the platform is at most 1.
       This is required to use interval lengths as a measure of service. *)
    Hypothesis no_parallelism:
      jobs_dont_execute_in_parallel sched.
    Hypothesis rate_at_most_one :
      forall j cpu, rate j cpu <= 1.

    (* Assumption: sporadic task model.
       This is necessary to conclude that consecutive jobs ordered by arrival times
       are separated by at least 'period' times units. *)
    Hypothesis sporadic_tasks: sporadic_task_model job_arrival job_task.

    (* Before starting the proof, let's give simpler names to the definitions. *)
    Definition response_time_bound_of (tsk: sporadic_task) (R: time) :=
      response_time_ub_task job_arrival job_cost job_task num_cpus rate
                            schedule_of_platform tsk R.
    Definition no_deadline_misses_by (tsk: sporadic_task) (t: time) :=
      task_misses_no_deadline_before job_arrival job_cost job_deadline job_task
                                     num_cpus rate sched tsk t.
    Definition workload_of (tsk: sporadic_task) (t1 t2: time) :=
      workload job_task rate num_cpus sched tsk t1 t2.

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
    Hypothesis valid_task_parameters: valid_sporadic_task tsk.

    (* Assumption: the task must have a restricted deadline.
       This is required to prove that n_k (max_jobs) from Bertogna
       and Cirinei's formula accounts for at least the number of
       middle jobs (i.e., number of jobs - 2 in the worst case). *)
    Hypothesis restricted_deadline: task_deadline tsk <= task_period tsk.

    (* Assume that a response-time bound R_tsk for that task in any
       schedule of this processor platform is also given. *)
    Variable R_tsk: time.
    Hypothesis response_time_bound: response_time_bound_of tsk R_tsk.
    Hypothesis response_time_bound_ge_cost: R_tsk >= task_cost tsk.
    
    (* Consider an interval [t1, t1 + delta), with no deadline misses. *)
    Variable t1 delta: time.
    Hypothesis no_deadline_misses_during_interval: no_deadline_misses_by tsk (t1 + delta).

    (* Then the workload of the task in the interval is bounded by W. *)
    Theorem workload_bound :
      workload_of tsk t1 (t1 + delta) <= W tsk R_tsk delta.
    Proof.
      rename jobs_have_valid_parameters into job_properties,
             no_deadline_misses_during_interval into no_dl_misses,
             valid_task_parameters into task_properties.
      unfold valid_sporadic_task_job, valid_realtime_job, restricted_deadline_model,
             valid_sporadic_taskset, valid_sporadic_task, sporadic_task_model,
             workload_of, response_time_bound_of, no_deadline_misses_by, W in *; ins; des.

      (* Simplify names *)
      set t2 := t1 + delta.
      set n_k := max_jobs tsk R_tsk delta.

      (* Use the definition of workload based on list of jobs. *)
      rewrite workload_eq_workload_joblist; unfold workload_joblist.
      
      (* Identify the subset of jobs that actually cause interference *)
      set interfering_jobs :=
        filter (fun x => (job_task x == tsk) && (service_during num_cpus rate sched x t1 t2 != 0))
                    (jobs_scheduled_between num_cpus sched t1 t2).
  
      (* Remove the elements that we don't care about from the sum *)
      assert (SIMPL:
        \sum_(i <- jobs_scheduled_between num_cpus sched t1 t2 | job_task i == tsk)
           service_during num_cpus rate sched i t1 t2 =
        \sum_(i <- interfering_jobs) service_during num_cpus rate sched i t1 t2).
      {
        unfold interfering_jobs.
        rewrite (bigID (fun x => service_during num_cpus rate sched x t1 t2 == 0)) /=.
        rewrite (eq_bigr (fun x => 0)); last by move => j_i /andP JOBi; des; apply /eqP.
        rewrite big_const_seq iter_addn mul0n add0n add0n.
        by rewrite big_filter.
      } rewrite SIMPL; clear SIMPL.

      (* Remember that for any job of tsk, service <= task_cost tsk *)
      assert (LTserv: forall j_i (INi: j_i \in interfering_jobs),
                        service_during num_cpus rate sched j_i t1 t2 <=
                        task_cost tsk).
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
      set order := fun x y => job_arrival x <= job_arrival y.
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
      assert (EX: exists elem: Job, True); des.
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
          rewrite [\sum_(_ <- _) service_during _ _ _ _ _ _]big_seq_cond.
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
            rewrite -[service_during _ _ _ _ _ _]addn0.
            apply leq_add; last by ins.
            apply leq_trans with (n := \sum_(t1 <= t < t2) 1).
              by apply leq_sum; ins; apply service_at_le_max_rate.
              by unfold t2; rewrite big_const_nat iter_addn mul1n addn0 addnC -addnBA // subnn addn0.
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
        by apply (sum_service_after_rt_zero job_arrival job_cost job_task)
                 with (response_time_bound := R_tsk) (tsk := tsk)
                      (schedule_of_platform := schedule_of_platform);
           last by apply ltnW.
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
        by unfold service_during; rewrite (sum_service_before_arrival job_arrival).
      }

      (* Next, we upper-bound the service of the first and last jobs using their arrival times. *)
      assert (BOUNDend: service_during num_cpus rate sched j_fst t1 t2 +
                        service_during num_cpus rate sched j_lst t1 t2 <=
                        (job_arrival j_fst  + R_tsk - t1) + (t2 - job_arrival j_lst)).
      {
        apply leq_add; unfold service_during.
        {
          rewrite -[_ + _ - _]mul1n -[1*_]addn0 -iter_addn -big_const_nat.
          apply leq_trans with (n := \sum_(t1 <= t < job_arrival j_fst + R_tsk)
                                         service_at num_cpus rate sched j_fst t);
            last by apply leq_sum; ins; apply service_at_le_max_rate.
          destruct (job_arrival j_fst + R_tsk <= t2) eqn:LEt2; last first.
          {
            unfold t2; apply negbT in LEt2; rewrite -ltnNge in LEt2.
            rewrite -> big_cat_nat with (n := t1 + delta) (p := job_arrival j_fst + R_tsk);
              [by apply leq_addr | by apply leq_addr | by apply ltnW].
          }
          {
            rewrite -> big_cat_nat with (n := job_arrival j_fst + R_tsk); [| by ins | by ins].
            rewrite -{2}[\sum_(_ <= _ < _) _]addn0 /=.
            rewrite leq_add2l leqn0; apply/eqP.
            by apply (sum_service_after_rt_zero job_arrival job_cost job_task)
                      with (response_time_bound := R_tsk) (tsk := tsk)
                           (schedule_of_platform := schedule_of_platform);
              last by apply leqnn.
          }
        }
        {
          rewrite -[_ - _]mul1n -[1 * _]addn0 -iter_addn -big_const_nat.
          destruct (job_arrival j_lst <= t1) eqn:LT.
          {
            apply leq_trans with (n := \sum_(job_arrival j_lst <= t < t2)
                                        service_at num_cpus rate sched j_lst t);
              first by rewrite -> big_cat_nat with (m := job_arrival j_lst) (n := t1);
                [by apply leq_addl | by ins | by apply leq_addr].
            by apply leq_sum; ins; apply service_at_le_max_rate.
          }
          {
            apply negbT in LT; rewrite -ltnNge in LT.
            rewrite -> big_cat_nat with (n := job_arrival j_lst); [|by apply ltnW| by apply ltnW].
            rewrite /= -[\sum_(_ <= _ < _) 1]add0n; apply leq_add.
            rewrite (sum_service_before_arrival job_arrival);
              [by apply leqnn | by ins | by apply leqnn].
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
                         service_during num_cpus rate sched (nth elem sorted_jobs i.+1) t1 t2 <=
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
            apply sporadic_tasks; last by ins.
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
            [rewrite leq_add2r leq_add2l; apply restricted_deadline | apply DISTmax].
        {
          (* Show that j_fst doesn't execute d_k units after its arrival. *)
          unfold t2; rewrite leq_add2r; rename completed_jobs into EXEC.
          unfold task_misses_no_deadline_before, job_misses_no_deadline, completed in *; des.
          exploit (no_dl_misses j_fst INfst); last intros COMP.
          { 
            (* Prove that arr_fst + d_k <= t2 *)
            apply leq_trans with (n := job_arrival j_lst); last by apply ltnW.
            apply leq_trans with (n := job_arrival j_fst + task_period tsk + delta); last by ins.
            rewrite -addnA leq_add2l -[job_deadline _]addn0.
            apply leq_add; last by ins.
            specialize (job_properties j_fst); des.
            by rewrite job_properties1 FSTtask restricted_deadline.
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
            apply leq_trans with (n := service num_cpus rate sched j_fst t2); last by apply EXEC.
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

  End ProofWorkloadBound.
  
End Workload.