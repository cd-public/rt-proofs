Require Import Vbase job task schedule task_arrival response_time platform
        schedulability divround helper priority identmp helper
        ssreflect ssrbool eqtype ssrnat seq div fintype bigop path ssromega.
  
(* Workload is defined as the total service received by jobs of
   a specific task in the interval [t,t'). *)
Definition workload (sched: schedule) (ts: taskset) (tsk: sporadic_task) (t t': time) :=
  \sum_(j <- prev_arrivals sched t' | job_task j == tsk) (service_during sched j t t').

(* Bound n_k on the number of jobs that execute completely in the interval *)
Definition max_jobs (tsk: sporadic_task) (R_tsk: time) (delta: time) :=
  div_floor (delta + R_tsk - task_cost tsk) (task_period tsk).

(* Bound on the workload of a task in an interval of length delta *)
Definition W (tsk: sporadic_task) (R_tsk: time) (delta: time) :=
  let n_k := (max_jobs tsk R_tsk delta) in
  let e_k := (task_cost tsk) in
  let d_k := (task_deadline tsk) in
  let p_k := (task_period tsk) in            
    minn e_k (delta + R_tsk - e_k - n_k * p_k) + n_k * e_k.

Section WorkloadBound.
  
Variable ts: taskset.
Variable sched: schedule.
Hypothesis sporadic_tasks: sporadic_task_model ts sched.
Hypothesis restricted_deadlines: restricted_deadline_model ts.

(* Assume a generic, but valid JLDP policy. This is required to derive that
   R_k >= e_k. *)
Variable higher_priority: sched_job_hp_relation.
Hypothesis valid_policy: valid_jldp_policy higher_priority.

(* Assume an identical multiprocessor with an arbitrary number of CPUs *)
Variable cpumap: job_mapping.
Variable num_cpus: nat.
Hypothesis sched_of_multiprocessor: ident_mp num_cpus higher_priority cpumap sched.

(* Let tsk be any task in the taskset. *)
Variable tsk: sporadic_task.
Hypothesis in_ts: tsk \in ts.

(* Suppose that we are given a response-time bound R_tsk for that task in any
   schedule of this processor platform. *)
Variable R_tsk: time.
Hypothesis response_time_bound:
  forall cpumap, response_time_ub (ident_mp num_cpus higher_priority cpumap) ts tsk R_tsk.

(* Consider an interval [t1, t1 + delta).*)
Variable t1 delta: time.
Hypothesis no_deadline_misses: task_misses_no_dl_before sched ts tsk (t1 + delta).

Theorem workload_bound : workload sched ts tsk t1 (t1 + delta) <= W tsk R_tsk delta.
Proof.
  rename sched_of_multiprocessor into MULT, sporadic_tasks into SPO, restricted_deadlines into RESTR,
         no_deadline_misses into NOMISS, higher_priority into hp.
  unfold sporadic_task_model, workload, W in *; ins; des.

  (* Simplify names *)
  set t2 := t1 + delta.
  set n_k := max_jobs tsk R_tsk delta.
  
  (* Name the subset of jobs that actually cause interference *)
  set interfering_jobs :=
    filter (fun x => (job_task x == tsk) && (service_during sched x t1 t2 != 0))
                    (prev_arrivals sched t2).
  
  (* Remove the elements that we don't care about from the sum *)
  assert (SIMPL:
    \sum_(i <- prev_arrivals sched t2 | job_task i == tsk)
       service_during sched i t1 t2 =
    \sum_(i <- interfering_jobs) service_during sched i t1 t2).
  {
    unfold interfering_jobs; rewrite (bigID (fun x => service_during sched x t1 t2 == 0)) /=.
    rewrite (eq_bigr (fun x => 0)); last by move => j_i /andP JOBi; des; apply /eqP.
    rewrite big_const_seq iter_addn mul0n add0n add0n.
    by rewrite big_filter.
  } rewrite SIMPL; clear SIMPL.

  (* Remember that for any job of tsk, service <= task_cost tsk *)
  assert (LTserv: forall j_i (INi: j_i \in interfering_jobs),
            service_during sched j_i t1 t2 <= task_cost tsk).
  {
    ins; move: INi; rewrite mem_filter; move => /andP xxx; des.
    move: xxx; move => /andP JOBi; des; clear xxx0 JOBi0.
    have PROP := job_properties j_i; des.
    move: JOBi => /eqP JOBi; rewrite -JOBi.
    apply leq_trans with (n := job_cost j_i); last by ins. 
    by apply service_interval_max_cost; unfold ident_mp in MULT; des.
  }

  (* Remember that R_tsk >= task_cost tsk in this platform *)
  assert (R_tsk >= task_cost tsk).
  {
    apply rt_geq_wcet_identmp with (ts := ts) (num_cpus := num_cpus) (hp := hp);
    by unfold ident_mp in MULT; des; ins.
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

  (* Remember that the jobs are ordered by arrival. We create some dummy job
     to use as default in nth. *)
  exploit (Build_job t2 1 (task_deadline tsk) tsk); last intros dummy.
    by repeat split; have PROP := task_properties tsk; des; ins.
  assert (ALL: forall i (LTsort: i < (size sorted_jobs).-1),
                 order (nth dummy sorted_jobs i) (nth dummy sorted_jobs i.+1)).
  by destruct sorted_jobs; [by ins| by apply/pathP; apply SORT].

  (* Now we start the proof. First, we show that the workload bound
     holds if n_k is no larger than the number of interferings jobs. *)
  destruct (size sorted_jobs <= n_k) eqn:NUM.
  {
    rewrite -[\sum_(_ <- _ | _) _]add0n leq_add //.
    apply leq_trans with (n := \sum_(x <- sorted_jobs) task_cost tsk);
      last by rewrite big_const_seq iter_addn addn0 mulnC leq_mul2r; apply/orP; right.
    {
      rewrite [\sum_(_ <- _) service_during _ _ _ _]big_seq_cond.
      rewrite [\sum_(_ <- _) task_cost _]big_seq_cond.
      by apply leq_sum; intros j_i; move/andP => xxx; des; apply LTserv; rewrite INboth.
    }
  }
  apply negbT in NUM; rewrite -ltnNge in NUM.

  (* Now we index the sum, so that we can access the first and last elements. *)
  rewrite (big_nth dummy).

  (* First and last only exist if there are at least 2 jobs. Thus, we must show
     that the bound holds for the empty list. *)
  destruct (size sorted_jobs) eqn:SIZE; [by rewrite big_geq // SIZE | rewrite SIZE].

  (* Let's derive some properties about the first element. *)
  exploit (mem_nth dummy); last intros FST.
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
        apply leq_trans with (n := job_cost (nth dummy sorted_jobs 0)).
        apply service_interval_max_cost; first by unfold ident_mp in MULT; des; ins.
        by rewrite -FSTtask; have PROP := job_properties (nth dummy sorted_jobs 0); des.
      }
      {
      rewrite -addnBA; last by ins.
      rewrite -[service_during _ _ _ _]addn0.
      apply leq_add; last by ins.
      unfold service_during; apply leq_trans with (n := \sum_(t1 <= t < t2) 1).
        by apply leq_sum; intros i _; unfold ident_mp in MULT; des; apply mp_max_service.
        by unfold t2; rewrite big_const_nat iter_addn mul1n addn0 addnC -addnBA // subnn addn0.
      }
    }
  } rewrite [nth]lock /= -lock in ALL.
  
  (* Knowing that we have at least two elements, we take first and last out of the sum *) 
  rewrite [nth]lock big_nat_recl // big_nat_recr // /= -lock.
  rewrite addnA addnC addnA.
  set j_fst := (nth dummy sorted_jobs 0).
  set j_lst := (nth dummy sorted_jobs n.+1).
                     
  (* Now we infer some facts about how first and last are ordered in the timeline *)
  assert (INfst: j_fst \in interfering_jobs).
    by unfold j_fst; rewrite INboth; apply mem_nth; destruct sorted_jobs; ins.
  move: INfst; rewrite mem_filter; move => /andP INfst; des.
  move: INfst => /andP INfst; des.

  assert (AFTERt1: t1 <= job_arrival j_fst + R_tsk).
  {
    rewrite leqNgt; apply /negP; unfold not; intro LTt1.
    move: INfst1 => /eqP INfst1; apply INfst1.
    unfold service_during.
    by rewrite (sum_service_after_rt (ident_mp num_cpus hp cpumap) sched ts MULT ARRts
                                           tsk j_fst INfst R_tsk); try apply ltnW.
  }
  assert (BEFOREt2: job_arrival j_lst < t2).
  {
    rewrite leqNgt; apply/negP; unfold not; intro LT2.
    assert (LTsize: n.+1 < size sorted_jobs).
      by destruct sorted_jobs; ins; rewrite SIZE; apply ltnSn.
    apply (mem_nth dummy) in LTsize; rewrite -INboth in LTsize.
    rewrite -/interfering_jobs mem_filter in LTsize.  
    move: LTsize => /andP xxx; des; move: xxx xxx0 => /andP xxx INlst; des.
    rename xxx0 into SERV; clear xxx.
    unfold service_during in SERV; move: SERV => /negP SERV; apply SERV.
    by rewrite sum_service_before_arrival.
  }

  (* Next, we upper-bound the service of the first and last jobs using their arrival times. *)
  assert(BOUNDend: service_during sched j_fst t1 t2 + service_during sched j_lst t1 t2 <=
                    (job_arrival j_fst  + R_tsk - t1) + (t2 - job_arrival j_lst)).
  {
    apply leq_add; unfold service_during.
    {
      rewrite -[_ + _ - _]mul1n -[1*_]addn0 -iter_addn -big_const_nat.
      apply leq_trans with (n := \sum_(t1 <= t < job_arrival j_fst + R_tsk)
                                     service_at sched j_fst t);
        last by apply leq_sum; unfold ident_mp in MULT; des; ins; apply mp_max_service.
      destruct (job_arrival j_fst + R_tsk <= t2) eqn:LEt2; last first.
      {
        unfold t2; apply negbT in LEt2; rewrite -ltnNge in LEt2.
        rewrite -> big_cat_nat with (n := t1 + delta) (p := job_arrival j_fst + R_tsk);
          [by apply leq_addr | by apply leq_addr | by apply ltnW].
      }
      {
        rewrite -> big_cat_nat with (n := job_arrival j_fst + R_tsk); [| by ins | by ins].
        rewrite -{2}[\sum_(_ <= _ < _) _]addn0 /=.
        apply leq_add; first by ins.
        by rewrite -> (sum_service_after_rt (ident_mp num_cpus hp cpumap) sched ts) with
                                            (R_tsk := R_tsk) (tsk := tsk); try apply leqnn.
      }
    }
    {
      rewrite -[_ - _]mul1n -[1 * _]addn0 -iter_addn -big_const_nat.
      destruct (job_arrival j_lst <= t1) eqn:LT.
      {
        apply leq_trans with (n := \sum_(job_arrival j_lst <= t < t2) service_at sched j_lst t);
          first by rewrite -> big_cat_nat with (m := job_arrival j_lst) (n := t1);
            [by apply leq_addl | by ins | by apply leq_addr].
        by apply leq_sum; unfold ident_mp in MULT; des; ins; apply mp_max_service.
      }
      {
        apply negbT in LT; rewrite -ltnNge in LT.
        rewrite -> big_cat_nat with (n := job_arrival j_lst); [|by apply ltnW| by apply ltnW].
        rewrite /= -[\sum_(_ <= _ < _) 1]add0n; apply leq_add.
        rewrite sum_service_before_arrival; [by ins | by apply leqnn].
        by apply leq_sum; unfold ident_mp in MULT; des; ins; apply mp_max_service.
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
  assert (BOUNDmid: \sum_(0 <= i < n) service_during sched (nth dummy sorted_jobs i.+1) t1 t2 <=
                      n * task_cost tsk).
  {
    apply leq_trans with (n := n * task_cost tsk);
      last by rewrite leq_pmul2r; [| have PROP := task_properties tsk; des].
    apply leq_trans with (n := \sum_(0 <= i < n) task_cost tsk);
      last by rewrite big_const_nat iter_addn addn0 mulnC subn0.
    rewrite big_nat_cond [\sum_(0 <= i < n) task_cost _]big_nat_cond.
    apply leq_sum; intros i; rewrite andbT; move => /andP LT; des.
    by apply LTserv; rewrite INboth mem_nth // SIZE ltnS leqW.
  }

  (* Conclude that the distance between first and last is at least n + 1 periods,
     where n is the number of middle jobs. *)
  assert (DIST: job_arrival j_lst - job_arrival j_fst >= n.+1*(task_period tsk)).
  {
    assert (EQnk: n.+1=(size sorted_jobs).-1); first by rewrite SIZE. 
    unfold j_fst, j_lst; rewrite EQnk telescoping_sum; last by rewrite SIZE.
    rewrite -[_ * _ tsk]addn0 mulnC -iter_addn -{1}[_.-1]subn0 -big_const_nat. 
    rewrite big_nat_cond [\sum_(0 <= i < _)(_-_)]big_nat_cond.
    apply leq_sum; intros i; rewrite andbT; move => /andP LT; des.
    {
      (* To simplify, call the jobs 'cur' and 'next' *)
      set cur := nth dummy sorted_jobs i.
      set next := nth dummy sorted_jobs i.+1.
      clear BOUNDend BOUNDmid LT LTserv NEXT j_fst j_lst INfst INfst0 INfst1
            AFTERt1 BEFOREt2 FSTserv FSTtask FSTin.

      (* Show that cur arrives earlier than next *)
      assert (ARRle: job_arrival cur <= job_arrival next).
      {
        unfold cur, next; rewrite -addn1; apply prev_le_next; first by rewrite SIZE.
        by apply leq_trans with (n := i.+1); try rewrite addn1.
      }
           
      (* Show that both cur and next are in the arrival sequence *)
      assert (INnth: cur \in interfering_jobs /\ next \in interfering_jobs).
      rewrite 2!INboth; split.
        by apply mem_nth, (ltn_trans LT0); destruct sorted_jobs; ins.
        by apply mem_nth; destruct sorted_jobs; ins.
      rewrite 2?mem_filter in INnth; des.
      rewrite 2?ts_finite_arrival_sequence // in INnth1 INnth3; unfold arrived_before in *.
      move: INnth1 INnth3 => /exists_inP_nat INnth1 /exists_inP_nat INnth3.
      destruct INnth1 as [arr_next [_ ARRnext]]; destruct INnth3 as [arr_cur [_ ARRcur]].
      generalize ARRnext ARRcur; unfold arrives_at in ARRnext, ARRcur; intros ARRnext0 ARRcur0.
      have arrPROP := arr_properties (arr_list sched); des.
      apply ARR_PARAMS in ARRnext; apply ARR_PARAMS in ARRcur.
      rewrite -> ARRnext in *; rewrite -> ARRcur in *.
      clear ARR_PARAMS NOMULT UNIQ.

      (* Use the sporadic task model to conclude that cur and next are separated
         by at least (task_period tsk) units. Of course this only holds if cur != next.
         Since we don't know much about the list (except that it's sorted), we must
         also prove that it doesn't contain duplicates. *)
      unfold t2 in ARRle.
      unfold interarrival_times in *; des.
      assert (CUR_LE_NEXT: arr_cur + task_period (job_task cur) <= arr_next).
      {
        apply INTER with (j' := next); try by ins.
        unfold cur, next, not; intro EQ; move: EQ => /eqP EQ.
        rewrite nth_uniq in EQ; first by move: EQ => /eqP EQ; intuition.
          by apply ltn_trans with (n := (size sorted_jobs).-1); destruct sorted_jobs; ins.
          by destruct sorted_jobs; ins.
          by rewrite sort_uniq -/interfering_jobs filter_uniq //; apply uniq_prev_arrivals.
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
        by apply ltnW, ltn_ceil; by have PROP := task_properties tsk; des.
      }
      apply leq_trans with (n.+1 * task_period tsk); last by apply DIST.
      by rewrite leq_pmul2r; [by ins | by have PROP := task_properties tsk; des].
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
        [by rewrite leq_add2r leq_add2l; apply RESTR | apply DISTmax].
    {
      (* Prove that j_fst does not execute d_k units after its arrival. *)
      unfold t2; rewrite leq_add2r.
      have PROP := arr_properties (arr_list sched); des.
      have PROP2 := sched_properties sched; des; rename comp_task_no_exec into EXEC.
      unfold task_misses_no_dl_before, job_misses_no_dl, completed in *; des.
      rewrite ts_finite_arrival_sequence in INfst0.
      move: INfst0 => /exists_inP_nat ARRIVED; destruct ARRIVED as [arr_fst [ARRfstLE ARRfst]].
      specialize (NOMISS1 j_fst FSTtask arr_fst ARRfst).
      specialize (ARR_PARAMS j_fst arr_fst ARRfst); rewrite -> ARR_PARAMS in *.
      exploit NOMISS1; last intros COMP.
      {
        (* Prove that arr_fst + d_k <= t2 *)
        apply leq_trans with (n := job_arrival j_lst); last by apply ltnW.
        apply leq_trans with (n := arr_fst + task_period tsk + delta); last by ins.
        rewrite -addnA leq_add2l -[job_deadline _]addn0.
        apply leq_add; last by ins.
        unfold restricted_deadline_model in RESTR.
        have PROP := job_properties j_fst; des.
        by rewrite job_params0 FSTtask RESTR.
      } red in COMP.
      rewrite leqNgt; apply/negP; unfold not; intro H2.
      clear task_must_arrive_to_exec ARRfst ARRfstLE BEFOREt2.
      assert (NOSERV: service_during sched j_fst t1 t2 = 0).
      {
        unfold service_during; apply/eqP; rewrite -leqn0.
        apply leq_trans with (n := \sum_(t1 <= t < t2) 0);
          last by rewrite big_const_nat iter_addn mul0n addn0 leqnn.
        {
          rewrite big_nat_cond [\sum_(_ <= _ < _) 0]big_nat_cond.
          apply leq_sum; intros i; rewrite andbT; move => /andP LTi; des.
          have PROP := job_properties j_fst; des. 
          specialize (EXEC j_fst i (arr_fst + job_deadline j_fst)).
          unfold completed in *; rewrite COMP in EXEC.
          exploit EXEC; last intro NOTSCHED; first by apply/eqP.
            by rewrite job_params0 FSTtask; apply leq_trans with (n := t1); [by apply ltnW|by ins].
          move: NOTSCHED; unfold scheduled; rewrite negbK; move => /eqP NOTSCHED.
          by rewrite NOTSCHED leqnn.
        }
      }
      by rewrite NOSERV in INfst1; move: INfst1 => /eqP INfst1; apply INfst1.
    }
  }

  (* With the facts that we derived, we can now prove the workload bound.
     There can be two cases since n <= n_k < n + 2, where n is the number
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
      rewrite NK ltnW // -ltn_divLR; last by have PROP := task_properties tsk; des.
      by unfold n_k, max_jobs, div_floor.
    }
    {
      rewrite -subnDA; apply leq_sub2l.
      apply leq_trans with (n := n.+1 * task_period tsk); last by apply DIST.
      rewrite -addn1 addnC mulnDl mul1n.
      by rewrite leq_add2l; last by have PROP := task_properties tsk; des. 
    }
  }
Qed.

End WorkloadBound.