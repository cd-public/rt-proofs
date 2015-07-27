Require Import Classical Vbase job task schedule task_arrival response_time platform
        schedulability divround helper priority identmp helper
        ssreflect ssrbool eqtype ssrnat seq div fintype bigop path ssromega.

Section WorkloadBound.
  
(* Workload is defined as the total service received by jobs of
   a specific task in the interval [t,t'). *)
Definition workload (sched: schedule) (ts: taskset) (tsk: sporadic_task) (t t': time) :=
  \sum_(j <- prev_arrivals sched t' | job_of tsk j) (service_during sched j t t').

Definition max_jobs (tsk: sporadic_task) (R_tsk: time) (delta: time) :=
  div_floor (delta + R_tsk - task_cost tsk) (task_period tsk).

Definition W (tsk: sporadic_task) (R_tsk: time) (delta: time) :=
  let n_k := (max_jobs tsk R_tsk delta) in
  let e_k := (task_cost tsk) in
  let d_k := (task_deadline tsk) in
  let p_k := (task_period tsk) in            
    minn e_k (delta + R_tsk - e_k - n_k * p_k) + n_k * e_k.

(* Returns the arrival time of a job that arrives before t'
   (or t' if the job doesn't arrive in the interval) *)
Definition arrival_time (sched: schedule) (t': time) (j: job) : nat :=
  find (arrives_at sched j) (iota 0 t').

Lemma max_jobs_bound :
  forall tsk delta R_tsk (GT: R_tsk >= task_cost tsk),
    (max_jobs tsk R_tsk delta).+1 >= div_ceil delta (task_period tsk).
Proof.
  unfold max_jobs, div_floor, div_ceil; ins.
  destruct (task_period tsk %| delta); [apply leqW | rewrite ltnS];
    by rewrite leq_div2r // -addnBA // leq_addr.
Qed.

Lemma max_num_jobs_ceil :
  forall ts sched (ARRts: ts_arrival_sequence ts sched)
         (RESTR: restricted_deadline_model ts) tsk (IN: tsk \in ts)
         (SCHED: task_misses_no_deadlines sched ts tsk) t1 t2,
    let released_jobs := filter (fun x => job_of tsk x &&
                                (service_during sched x t1 t2 != 0)) (prev_arrivals sched t2) in  
    size released_jobs <= div_ceil (t2 - t1) (task_period tsk).
Proof.
  ins.
Admitted.



      
Lemma workload_bound :
  forall ts sched (ARRts: ts_arrival_sequence ts sched)
         hp (VALIDhp: valid_jldp_policy hp)
         cpumap num_cpus (MULT: ident_mp num_cpus hp cpumap sched)
         (RESTR: restricted_deadline_model ts)
         tsk (IN: tsk \in ts) j (JOB: job_task j = tsk)
         arr_j (ARRj: arrives_at sched j arr_j)
         (NOMISS: task_misses_no_deadlines sched ts tsk)
         R_tsk (RESP: forall mapped,
               response_time_ub (ident_mp num_cpus hp mapped) ts tsk R_tsk),
    (workload sched ts tsk arr_j (arr_j + job_deadline j)) <=
       W tsk R_tsk (job_deadline j).
Proof.
  unfold workload, W; ins.

  (* Simplify names *)
  set t1 := arr_j.
  set t2 := arr_j + job_deadline j.
  set n_k := max_jobs tsk R_tsk (job_deadline j).

  (* Remember the maximum number of jobs that contribute to the workload *)
  have CEIL := max_num_jobs_ceil ts sched ARRts RESTR tsk IN NOMISS t1 t2;
  simpl in *.

  (* Use a simpler name for the set of jobs that we are interested in *)
  set released_jobs :=
    filter (fun x => job_of tsk x && (service_during sched x t1 t2 != 0))
                    (prev_arrivals sched t2); fold released_jobs in CEIL.
  
  (* Remove the elements that we don't care about from the sum *)
  assert (SIMPL:
    \sum_(i <- prev_arrivals sched t2 | job_of tsk i)
       service_during sched i t1 t2 =
    \sum_(i <- released_jobs) service_during sched i t1 t2).
  {
    unfold released_jobs.
    rewrite (bigID (fun x => service_during sched x t1 t2 == 0)) /=.
    rewrite (eq_bigr (fun x => 0));
      last by move => j_i /andP JOBi; des; apply /eqP.
    rewrite big_const_seq iter_addn mul0n add0n add0n.
    by rewrite big_filter.
  } rewrite SIMPL; clear SIMPL.

  (* Remember that for any job of tsk, service <= task_cost tsk *)
  assert (LTserv: forall j_i (INi: j_i \in released_jobs),
            service_during sched j_i t1 t2 <= task_cost tsk).
  {
    ins; move: INi; rewrite mem_filter; move => /andP xxx; des.
    move: xxx; move => /andP JOBi; des; clear xxx0 JOBi0.
    have PROP := job_properties j_i; unfold job_of in *; des.
    apply leq_trans with (n := job_cost j_i);
      last by unfold beq_task in *; destruct task_eq_dec as [EQ|]; try rewrite -EQ; ins.
    by apply service_interval_max_cost; unfold ident_mp in MULT; des.
  }

  (* Remember that R_tsk >= task_cost tsk in this platform *)
  assert (R_tsk >= task_cost tsk).
  {
    apply rt_geq_wcet_identmp with (ts := ts)
                                 (num_cpus := num_cpus) (hp := hp);
    unfold ident_mp in MULT; des; ins.
  }

  assert (EQdelta: t2 - t1 = job_deadline j).
    by unfold t1,t2; rewrite addnC -addnBA // subnn addn0.

  (* Now we begin the proof. *)
  (* Let num_jobs = (size released_jobs). Then, either (1) num_jobs <= n_k, or (2) num_jobs > n_k. *)
  (*remember (size released_jobs) as num_jobs*)
  set num_jobs := size released_jobs. 
  destruct (num_jobs <= n_k) eqn:NUM.
  {
    rewrite -[\sum_(_ <- _ | _) _]add0n leq_add //.
    apply leq_trans with (n := \sum_(x <- released_jobs) task_cost tsk);
      last by rewrite big_const_seq iter_addn addn0 mulnC leq_mul2r;
      apply/orP; right.
    {
      rewrite big_seq_cond [\sum_(_ <- _ | _) _ _]big_seq_cond.
      by apply leq_sum; intros j_i; move/andP => xxx; des; apply LTserv.
    }
  }
  {
    (* Since num_jobs cannot be larger than n_k.+1, it must be equal to n_k.+1 *)
    assert (EQnum: num_jobs == n_k.+1).
    {
      apply negbT in NUM; rewrite -ltnNge in NUM.
      rewrite eqn_leq; apply/andP; split; last by ins.
      apply leq_trans with (n := div_ceil (job_deadline j) (task_period tsk));
      [by rewrite -EQdelta | by apply max_jobs_bound].
    } clear NUM.
    
    (* Order the sequence of released_jobs by arrival time, so that
       we identify easily the first and last jobs. *)
    set order := fun x y => arrival_time sched t2 x <= arrival_time sched t2 y.
    set sorted_jobs := (sort order released_jobs).
    assert (sorted: sorted order sorted_jobs);
      first by apply sort_sorted; unfold total, order; ins; apply leq_total.
    rewrite (eq_big_perm sorted_jobs) /=; last by rewrite -(perm_sort order).

    (* State that the sorted list has the same size as the old one *)
    set num_jobs_s := size sorted_jobs.                 
    assert (EQ: num_jobs = num_jobs_s).
      by apply perm_eq_size; rewrite -(perm_sort order).
    rewrite -> EQ in *. clear EQ num_jobs.
    rename num_jobs_s into num_jobs; simpl in *.

    (* Remember that they have the same set of elements *)
    assert (INboth: forall x, (x \in released_jobs) = (x \in sorted_jobs)).
      by apply perm_eq_mem; rewrite -(perm_sort order).

    (* Index the sequence *)
    rewrite (big_nth j); fold num_jobs.
  
    (* Show that the inequality holds if there's a single element in the list. *)
    move: EQnum => /eqP EQnum; rewrite EQnum; unfold num_jobs in EQnum.
    destruct n_k.
    {
      rewrite big_nat_recl // big_geq // 2!mul0n subn0 2!addn0.
      rewrite leq_min; apply/andP; split; first by apply LTserv; rewrite INboth mem_nth // EQnum.
      rewrite -addnBA // -[service_during sched _ _ _]addn0.
      apply leq_add; last by ins.
      unfold service_during; apply leq_trans with (n := \sum_(t1 <= t < t2) 1).
      apply leq_sum; ins; first by unfold ident_mp in MULT; des; apply mp_max_service.
      by rewrite big_const_nat iter_addn mul1n addn0 -EQdelta.
    }
    
    (* Take first and last elements out of the sum *) 
    rewrite [nth]lock big_nat_recl // big_nat_recr // /= -lock.

    (* Move one (task_cost tsk) term inside the min *)
    rewrite [_ * task_cost _]mulSn [_ + (task_cost _ + _)]addnA addn_minl.
    rewrite addnA -addnC addnA.

    (* Bound the service of the middle jobs *)
    apply leq_add; last first.
    {
      apply leq_trans with (n := \sum_(0 <= i < n_k) task_cost tsk);
        last by rewrite big_const_nat iter_addn addn0 mulnC subn0.
      rewrite big_nat_cond [\sum_(0 <= i < n_k) task_cost _]big_nat_cond.
      apply leq_sum; intros i; rewrite andbT; move => /andP LT; des.
      by apply LTserv; rewrite INboth mem_nth // EQnum ltnS; apply (leq_trans LT0).
    }
    {
      (* Bound the service of the first and last jobs *)
      rewrite leq_min; apply/andP; split;
      first by apply leq_add; apply LTserv; rewrite INboth mem_nth // EQnum.
      {
        (* Prove the right side of the min *)
        set j_fst := (nth j sorted_jobs 0).
        set j_lst := (nth j sorted_jobs n_k.+1).
        apply leq_trans with (n := (arrival_time sched t2 j_fst  + R_tsk - t1) +
                                   (t2 - arrival_time sched t2 j_lst)).
        {
          apply leq_add; unfold service_during.
          admit.
          admit.
        }
        {
          rewrite [_ - _ + task_cost _]subh1; last by admit.
          rewrite [_ - _ + task_cost _]subh1; last first.
          {
            rewrite -[task_cost _]addn0.
            apply leq_add; last by ins.
            have PROP := job_properties j; des.
            rewrite job_params0 JOB.
            by have PROP2 := task_properties tsk; des.
          }
          rewrite -[_ + _ - task_cost _]addnBA // subnn addn0.
          rewrite addnC.
          rewrite -
          apply leq_trans with (n := job_deadline j + R_tsk
 
          rewrite subnn. simpl. ; apply leq_add. [task]
          rewrite -addnBA. -subnBA.
        }
      }
    }
  }
Qed.    

    (*rewrite addn_minl.
    rewrite addn_minr leq_min; apply/andP; split.
    
    (* Break the list at both sides, so that we get the first and last elements. *)
    destruct sorted_jobs as [| j_fst]; simpl in *; first by rewrite big_nil.
    rewrite big_cons.
    destruct (lastP sorted_jobs) as [| middle j_lst].
    {
      (* If last doesn't exist, show that the the bound holds for the first element *) 
      rewrite big_nil addn0.
      rewrite eqSS /= in EQnum; simpl in EQnum.
      move: EQnum => /eqP EQnum; rewrite -EQnum.
      rewrite 2!mul0n subn0 addn0.
      rewrite leq_min; apply/andP; split;
        first by apply LTserv; rewrite INboth mem_seq1; apply/eqP.
      rewrite -addnBA; last by ins.
      {
        rewrite -[service_during sched j_fst t1 t2]addn0.
        rewrite leq_add //.
        apply leq_trans with (n := \sum_(t1 <= t < t2) 1).
          by apply leq_sum; unfold ident_mp in MULT; des; ins;
            apply mp_max_service. 
          by rewrite sum_nat_const_nat muln1 leq_subLR.
      }
    } 

    (* Remember the minimum distance between the arrival times of first and last *)
    assert (ARRfst: exists arr_fst, arrives_at sched j arr_fst). admit.
    assert (ARRlst: exists arr_lst, arrives_at sched j arr_lst). admit. des.
    assert (DIST: arr_lst - arr_fst >= n_k * (task_period tsk)). admit.
    assert (LTlst: arr_lst < t2). admit.
     *)
    
    (* Align the inequality so that we map (first, middle, last) with their respective bounds.
       We split the n_k*e_k as: e_k + (n_k - 1)*n_k. For that, we need to destruct n_k. *)
    (*rewrite -cats1 big_cat big_cons big_nil /=.
    rewrite addn0 addnC -addnA [_ + (_ * _)]addnC.
    destruct n_k; first by rewrite eqSS in EQnum;
      move: EQnum => /nilP EQnum; destruct middle; inversion EQnum.     
    rewrite mulSnr -addnA.
    apply leq_add.
    {
      (* Show that the total service received by middle <= n_k * task_cost *)
      rewrite big_seq_cond.
      apply leq_trans with (n := \sum_(i <- middle | (i \in middle) && true) task_cost tsk).
      {
        apply leq_sum; intro j_i; move => /andP MID; des; apply LTserv.
        specialize (INboth j_i); rewrite INboth in_cons mem_rcons in_cons.
        by apply/or3P; apply Or33.
      }
      {
        rewrite -big_seq_cond big_const_seq iter_addn addn0 mulnC leq_mul2r; apply/orP; right.
        rewrite count_predT; rewrite eqSS size_rcons eqSS in EQnum.
        by move: EQnum => /eqP EQnum; rewrite -EQnum leqnn.
      }
    }
    {
      (* Show that the service of first and last is bounded by the min() expression. *)
      rewrite addn_minr leq_min; apply/andP; split.
      {
        (* Left side of the min() is easy. *)
        apply leq_add; apply LTserv;
        [specialize (INboth j_lst) | specialize (INboth j_fst)];
        rewrite INboth in_cons mem_rcons in_cons; apply/or3P;
        [by apply Or32 | by apply Or31].
      }
      {
        (* Now we prove the right side of the min(). We need to find the
           minimum distance between the arrival times of first and last *)
        move: sorted; rewrite rcons_path; move => /andP sorted; des.
        (*
        apply leq_trans with (n := (arr_fst + R_tsk - t1) + (t2 - arr_lst)).
        {
          apply leq_add.
          {
            admit.
          }
          {
            admit.
          }
        }
        {
          rewrite addnC. rewrite addnBA.
          rewrite addnC.
          rewrite -addnBA. rewrite subnAC.
          assert (EQ: t2 - t1 = job_deadline j);
            [by unfold t1,t2; rewrite addnC -addnBA // subnn addn0|]; rewrite EQ; clear EQ.
         
          rewrite -[(t2 - arr_list) - t1]subnDA. -subnAC. rewrite -subnBA. AC.
          rewrite -subnBA.
          rewrite
          rewrite -subnAC.
          rewrite addnBA; last by apply ltnW.
          rewrite -[arr_fst + R_tsk - t1]addnBA.
          rewrite -addnA. rewrite 
          rewrite -addnBA. rewrite addnC.
          
          rewrite [(R_tsk - t1) + t2]addnC. rewrite -subnAC.
          rewrite addnA. -subnBA. *)
        admit.
        (*rewrite addnBA. rewrite addnBA. rewrite [task_cost _ + _]addnC.
        rewrite -addnBA. rewrite subnn addn0.
        admit.*) 
      }
    }
  }
Qed.*)

End WorkloadBound.