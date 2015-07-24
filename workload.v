Require Import Classical Vbase job task schedule task_arrival response_time platform
        schedulability divround helper priority identmp
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

(* A carried-in job in [t1,t2) arrives before t1 and is not completed at time t1 *)
Definition carried_in (sched: schedule) (tsk: sporadic_task) (t1: time) (j: job) :=
  [&& job_task j == tsk, arrived_before sched j t1 & ~~ completed sched j t1].

(* A carried-out job in [t1,t2) arrives after t1 and is not completed at time t2 *)
Definition carried_out (sched: schedule) (tsk: sporadic_task) (t1 t2: time) (j: job) :=
  [&& job_task j == tsk, arrived_between sched j t1 t2 & ~~ completed sched j t2].

(* Returns the arrival time of a job that arrives before t'
   (or t' if the job doesn't arrive in the interval) *)
Definition arrival_time (sched: schedule) (t': time) (j: job) : nat :=
  find (arrives_at sched j) (iota 0 t').

Definition my_service_at (my_j: job) (j: job) : time -> nat :=
  if my_j == j then
    (fun t => (if t < task_cost (job_task j) then 1 else 0))
  else (fun t => 0).

Definition my_arr_seq (my_j: job) : nat -> seq job :=
  fun t => if (t == 0) then [::my_j] else [::].

Lemma rt_geq_wcet_identmp : (* The definition of platform is wrong, shouldn't have hp and cpumap *)
  forall ts tsk R_tsk num_cpus hp cpumap
         (RESP: response_time_ub_task (ident_mp num_cpus hp cpumap) ts tsk R_tsk),
    R_tsk >= task_cost tsk.  
Proof.
  unfold response_time_ub_task; ins; des.
  have PROP := task_properties tsk; des.
  have tmp_job := Build_job (task_cost tsk) (task_deadline tsk) tsk.

  assert (VALIDj:  << X1: 0 < task_cost tsk >> /\
                   << X2: task_cost tsk <= task_deadline tsk >> /\
                   << X3: 0 < task_deadline tsk >> /\
                   << X4: task_cost tsk <= task_cost tsk >> /\
                   << X5: task_deadline tsk = task_deadline tsk >> ).
    by repeat split; ins; try apply leqnn; clear tmp_job; rename x0 into j.
    
  set j := Build_job (task_cost tsk) (task_deadline tsk) tsk VALIDj.

  assert (NOMULT: (forall (j0 : job_eqType) (t1 t2 : time),
             j0 \in my_arr_seq j t1 -> j0 \in my_arr_seq j t2 -> t1 = t2)).
    by ins; unfold my_arr_seq in *; destruct t1, t2; simpl in *; ins.
  set arr := Build_arrival_sequence (my_arr_seq j) NOMULT.

  assert (VALID: (<< BLA: forall (j0 : job) (t : time),
   scheduled {| service_at := my_service_at j; arr_list := arr |} j0 t ->
   arrived {| service_at := my_service_at j; arr_list := arr |} j0 t >> /\   
    << BLA2: forall (j0 : job) (t : nat) (t_comp : time),
   completed {| service_at := my_service_at j; arr_list := arr |} j0 t_comp ->
   t_comp <= t ->
   ~~ scheduled {| service_at := my_service_at j; arr_list := arr |} j0 t >> )).
  {
    repeat (split; try red).
    {
      intros j0 t SCHED.
      unfold scheduled, arrived in *; apply/exists_inP_nat.
      unfold service_at, my_service_at in SCHED.
      destruct (j == j0) eqn:EQj_j0; last by move: SCHED => /eqP SCHED; intuition.
      destruct (t < task_cost (job_task j0)) eqn:LE; last by move: SCHED => /eqP SCHED; intuition.
      exists 0; split; first by apply ltn0Sn.
      unfold arrives_at, arr_list, arr, my_arr_seq; simpl.
      move: EQj_j0 => /eqP EQj_j0; subst.
      by rewrite mem_seq1; apply/eqP.
    }
    {
      unfold completed, service; intros j0 t t_comp COMPLETED LE.
      unfold scheduled, service_at, my_service_at.
      destruct (j == j0) eqn:EQj_j0; last by apply negbT; apply/eqP.
      move: EQj_j0 => /eqP EQj_j0; subst j0.
      apply negbT; apply/eqP.
      have PROP := job_properties j; des; simpl in *.
      destruct (t < task_cost tsk) eqn:LEcost; last by trivial.
        assert (t_comp < task_cost tsk).
          by apply leq_trans with (n := t.+1); [by rewrite ltnS | by ins].
        move: COMPLETED => /eqP COMPLETED; rewrite <- COMPLETED in *.
        assert (t_comp < t_comp).
        apply leq_trans with (n := \sum_(0 <= t0 < t_comp) my_service_at j j t0); first by ins.
        apply leq_trans with (n := \sum_(0 <= t0 < t_comp) 1).
          apply leq_sum. admit.
          by rewrite big_const_nat iter_addn mul1n addn0 subn0.
      by rewrite ltnn in H0; ins.
    }
  }
  
  set sched := Build_schedule (Build_schedule_data (my_service_at j) arr) VALID.

  assert (ARRts: ts_arrival_sequence ts sched). admit.

  assert (my_cpumap: job_mapping). admit. (* Map always to cpu 0 *)
  
  assert (MULT: ident_mp num_cpus hp cpumap sched). admit.

Admitted.

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



Lemma telescoping_sum : forall (T: Type) F r (x0: T),
              F (nth x0 r (size r).-1) - F (nth x0 r 0) =
                \sum_(i < (size r).-1) (F (nth x0 r (i.+1)) - F (nth x0 r i)).
Proof.
  intros T F r x0.

  assert (forall (i j: nat) (LE: i <= j), F (nth x0 r i) <= F (nth x0 r j)). admit.

  induction r.
    by rewrite subnn big_ord0.
    
  
  destruct r.
    by rewrite subnn big_ord0.
    induction r.
      by rewrite subnn big_ord0.
      
  
  generalize dependent r.
  induction r.
    by rewrite subnn big_ord0.
    ins.
    assert (r = behead (a :: r)). admit.
    exploit IHr. intros i j LE.
    rewrite H0.
    rewrite 2!nth_behead.
    apply H. ins.
    intro IH.
    rewrite H0 in IH.
    rewrite nth_behead in IH.
    destruct r.
      by rewrite subnn big_ord0.

    rewrite big_ord_recl; simpl in *.
    rewrite -IH.
    rewrite addnBA; last first.
    specialize (H 1 (size r)).
    exploit H; ins.
    unfold nth.

  -addnA.
      rewrite <- eqn_add2r with (p := F a).
      rewrite addnC. rewrite addnBA.
      exploit IHr.
      ins. destruct nth.
      unfold nth.
      destruct s.
 
        rewrite -eqn_add2r.
  destruct r.
    by rewrite subnn big_ord0.
  destruct r.
    by rewrite subnn big_ord0.
  induction r.
    simpl in *. rewrite big_ord_recl. simpl in *.
     by rewrite big_ord0 addn0.

    repeat rewrite big_ord_recl.
    simpl in *.
    rewrite big_ord_recl in IHr.
    simpl in *.
     induction r.
    by rewrite subnn big_ord0.
     rewrite -big_ord_recl.
  
  
  destruct r.
    by rewrite subnn big_ord0.
  
  induction r.
    by rewrite subnn big_ord0. 
    simpl in *.
    rewrite -> nth_last in *.
    rewrite -> last_cons in *.
    destruct r.
      by rewrite big_ord_recl big_ord0 addn0; simpl in *.
      simpl in *.
      rewrite IHr. simpl in *.

      rewrite big_ord_recl. rewrite big_ord_recl. rewrite big_ord_recl.
      simpl in *.
      rewrite addnA. simpl in *.
      rewrite [(_ - _) + (_ - _)]addnC.
      rewrite addnBA.



      
Lemma workload_bound :
  forall ts sched (ARRts: ts_arrival_sequence ts sched)
         hp cpumap num_cpus (MULT: ident_mp num_cpus hp cpumap sched) 
         (RESTR: restricted_deadline_model ts)
         tsk (IN: tsk \in ts) j (JOB: job_task j = tsk)
         arr_j (ARRj: arrives_at sched j arr_j)
         (NOMISS: task_misses_no_deadlines sched ts tsk)
         R_tsk (RESP: response_time_ub_task (ident_mp num_cpus hp cpumap) ts tsk R_tsk),
    (workload sched ts tsk arr_j (arr_j + job_deadline j)) <= W tsk R_tsk (job_deadline j).
Proof.
  unfold workload, W; ins.

  (* Simplify names *)
  set t1 := arr_j.
  set t2 := arr_j + job_deadline j.
  set n_k := max_jobs tsk R_tsk (job_deadline j).

  (* Remember the maximum number of jobs that contribute to the workload *)
  have CEIL := max_num_jobs_ceil ts sched ARRts RESTR tsk IN NOMISS t1 t2; simpl in *.

  (* Use a simpler name for the set of jobs that we are interested in *)
  set released_jobs := filter (fun x => job_of tsk x && (service_during sched x t1 t2 != 0))
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
  generalize RESP; apply rt_geq_wcet_identmp in RESP; intro RT_WCET.

  (* Now we begin the proof. *)
  (* Let num_jobs = (size released_jobs). Then, either (1) num_jobs <= n_k, or (2) num_jobs > n_k. *)
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
      last by apply max_jobs_bound with (platform:= ident_mp num_cpus hp cpumap)
              (ts:= ts) (delta := job_deadline j); have PROP := job_properties j; des; ins.
      assert (EQ: t2 - t1 = job_deadline j); [by unfold t1,t2; rewrite addnC -addnBA // subnn addn0|].
      by rewrite -EQ.
    }
    
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

    Require Import tuple.
    (* Index the sequence, so we can easily establish properties
       about consecutive elements. *)

    rewrite (big_nth j).
   

    F service_during sched (tnth (in_tuple sorted_jobs) i) t1 t2 <=
   minn (task_cost tsk)
     (job_deadline j + R_tsk - task_cost tsk - n_k * task_period tsk) +
   n_k * task_cost tsk

                   
    assert (forall l (l = fst :: mid ++ [:: lst]),
             F lst - F fst = \sum(size - 1)

                          i1 (*(LT1: i1 < size sorted_jobs)*)
                        i2 (*(LT2: i2 < size sorted_jobs)*)
                        k (DIST: i2 = i1 + k),
                   arrival_time sched t2 (nth j sorted_jobs i2) >=
                   arrival_time sched t2 (nth j sorted_jobs i1) +
                   (i2-i1)*(task_period tsk)).
    
    (*rewrite (big_nth j).
    assert (IND: forall i1 (*(LT1: i1 < size sorted_jobs)*)
                        i2 (*(LT2: i2 < size sorted_jobs)*)
                        k (DIST: i2 = i1 + k),
                   arrival_time sched t2 (nth j sorted_jobs i2) >=
                   arrival_time sched t2 (nth j sorted_jobs i1) +
                   (i2-i1)*(task_period tsk)).
    induction i2; ins.
      rewrite sub0n mul0n addn0.
    induction k; ins.
      admit.
    (*generalize dependent i2. generalize dependent i1.*)
    ins. generalize dependent i2. generalize dependent k.
    induction k; ins.
      by rewrite DIST addn0 subnn mul0n addn0 leqnn.
      apply IHk.
      destruct i2. admit.
      
      apply IHk.
    
      remember (i2 - i1) as dist.
      generalize dependent i2. generalize dependent i1. generalize dependent dist.
      induction dist; ins.
      {
        assert (EQ: i1 = i2).
          symmetry in Heqdist; move: Heqdist => /eqP Heqdist; rewrite subn_eq0 in Heqdist. 
          by apply/eqP; rewrite eqn_leq; apply/andP; split.
        by rewrite EQ mul0n addn0 leqnn.
      }
      {
        apply IHdist. 
        unfold arrival_time. 
          assert (EQ': LT1 <-> LT2).
          rewrite mul0n addn0.
          subst. rewrite EQ in LT1. rewrite -> EQ in *. LT12 /\ Heqdist).
      
      set dist := i2 - i1.
      induction dist.

    assert (IND: forall i1 (LT1: i1 < size sorted_jobs)
                        i2 (LT2: i2 < size sorted_jobs)
                        (LT12: i1 < i2),
                   arrival_time sched t2 (tnth (in_tuple sorted_jobs) i1) >=
                   arrival_time sched t2 (tnth (in_tuple sorted_jobs) i2) +
                   (i2-i1)*(task_period tsk)).
      induction i1 as [i]; ins.
        induction i2 as [i']; ins.

    *)

    assert (IND: forall i1 (*(LT1: i1 < size sorted_jobs)*)
                        i2 (*(LT2: i2 < size sorted_jobs)*)
                        k (DIST: i2 = i1 + k),
                   arrival_time sched t2 (nth j sorted_jobs i2) >=
                   arrival_time sched t2 (nth j sorted_jobs i1) +
                   (i2-i1)*(task_period tsk)).

    
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
    
    (* Align the inequality so that we map (first, middle, last) with their respective bounds.
       We split the n_k*e_k as: e_k + (n_k - 1)*n_k. For that, we need to destruct n_k. *)
    rewrite -cats1 big_cat big_cons big_nil /=.
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
          rewrite addnA. -subnBA.
        admit.
        (*rewrite addnBA. rewrite addnBA. rewrite [task_cost _ + _]addnC.
        rewrite -addnBA. rewrite subnn addn0.
        admit.*) 
      }
    }
  }
Qed.

End WorkloadBound.