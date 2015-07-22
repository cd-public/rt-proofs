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

Check Build_schedule_data.


Print Build_schedule_data. (* service_at : job -> time -> nat *)

Check Build_arrival_sequence.
Definition my_service_at (my_j: job) (j: job) : time -> nat :=
  if my_j == j then
    (fun t => (if t < task_cost (job_task j) then 1 else 0))
  else (fun t => 0).

Definition my_arr_seq (my_j: job) : nat -> seq job :=
  fun t => if (t == 0) then [::my_j] else [::].

Lemma floorS :
  forall m n (GTm: m > 0) (GTn: n > 0), div_floor (n + m - 1) m = (div_floor (n-1) m).+1.
Proof.
  destruct m; first by ins.
  destruct n; first by ins.
  generalize dependent m. generalize dependent n.
  unfold div_floor; induction m; ins.
  {
    rewrite 2!divn1 -[(_ - _).+1]addn1.
    rewrite -subnBA // subnn subn0 -[n.+1]addn1.
    by rewrite -addnBA // subnn addn0.
  }
  {
    rewrite -[m.+2]addn1.
    rewrite -addnBA //.
    rewrite -subnBA //.
    rewrite subnn subn0.
Admitted.

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
  forall platform ts tsk delta
         (GTdelta: delta > 0)
         R_tsk (RESP: response_time_ub_task platform ts tsk R_tsk)
         (GT: R_tsk >= task_cost tsk),
    (max_jobs tsk R_tsk delta).+1 >= div_ceil delta (task_period tsk).
Proof.
  unfold max_jobs, div_floor, div_ceil; ins.
  have PROP := task_properties tsk; des.
  destruct task_cost as [|e]; first by intuition.
  apply ltnW in GT.
  rewrite -[e.+1]addn1 subnDA -floorS //; unfold div_floor; last first.
    by rewrite -addnBA //; apply leq_trans with (n := delta); rewrite // leq_addr.
  rewrite leq_div2r // -2?addnBA // leq_add2r.
  by rewrite -addnBA // leq_addr.
Qed.
    
Lemma workload_bound :
  forall ts sched (ARRts: ts_arrival_sequence ts sched)
         hp cpumap num_cpus (MULT: ident_mp num_cpus hp cpumap sched) 
         (RESTR: restricted_deadline_model ts)
         tsk (IN: tsk \in ts) j (JOB: job_task j = tsk)
         arr_j (ARRj: arrives_at sched j arr_j)
         (SCHED: task_misses_no_deadlines sched ts tsk)
         R_tsk (RESP: response_time_ub_task (ident_mp num_cpus hp cpumap) ts tsk R_tsk),
    (workload sched ts tsk arr_j (arr_j + job_deadline j)) <= W tsk R_tsk (job_deadline j).
Proof.
  unfold workload, W; ins.

  (* Simplify names *)
  set t1 := arr_j.
  set t2 := arr_j + job_deadline j.
  set n_k := max_jobs tsk R_tsk (job_deadline j).

  (* Focus only on the jobs of tsk that contribute to the workload *)
  set released_jobs := filter (fun x => job_of tsk x && (service_during sched x t1 t2 != 0)) (prev_arrivals sched t2).

  (* Prune the sequence to remove elements that we don't care about *)
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

  (* Small lemma that is reused many times *)
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

  (* Remember that R_tsk in this platform is no less than the WCET of the task *)
  generalize RESP; apply rt_geq_wcet_identmp in RESP; intro RT_WCET.
  
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
    (* Hard case: num_jobs with service > 0 in the interval more than n_k *)
    assert (EQnum: num_jobs == n_k.+1).
    {
      apply negbT in NUM; rewrite -ltnNge in NUM.
      rewrite eqn_leq; apply/andP; split; last by ins.
      apply leq_trans with (n := div_ceil (job_deadline j) (task_period tsk));
      last by apply max_jobs_bound with (platform:= ident_mp num_cpus hp cpumap)
              (ts:= ts) (delta := job_deadline j); have PROP := job_properties j; des; ins.

      (* Prove that the maximum number of jobs is ceil(\Delta)(p_k)*)
      admit.
    }
    
    (* Order the sequence of released_jobs by arrival time, so that
       we identify easily the first and last jobs. *)
    set order := fun x y =>
                   arrival_time sched t2 x <= arrival_time sched t2 y.
    set sorted_jobs := (sort order released_jobs).
    assert (sorted: sorted order sorted_jobs);
      first by apply sort_sorted; unfold total, order; ins; apply leq_total.
    rewrite (eq_big_perm sorted_jobs) /=;last by rewrite -(perm_sort order).

    (* Restate the size of the new list *)
    set num_jobs_s := size sorted_jobs.                 
    assert (EQ: num_jobs = num_jobs_s).
      by apply perm_eq_size; rewrite -(perm_sort order).
    rewrite -> EQ in *. clear EQ num_jobs.
    rename num_jobs_s into num_jobs; simpl in *.

    assert (INboth: forall x, (x \in released_jobs) = (x \in sorted_jobs)).
      by apply perm_eq_mem; rewrite -(perm_sort order).

    (* Destruct sorted_jobs at the beginning and at the end,
       so that we get the first and last elements. *)
    destruct sorted_jobs as [| j_fst]; simpl in *; first by rewrite big_nil.
    rewrite big_cons.
    destruct (lastP sorted_jobs) as [| middle j_lst].
    {
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

    rewrite -cats1 big_cat big_cons big_nil /=.
    rewrite addn0 addnC -addnA [_ + (_ * _)]addnC.
    destruct n_k; first by rewrite eqSS in EQnum;
      move: EQnum => /nilP EQnum; destruct middle; inversion EQnum.     
    rewrite mulSnr -addnA.
    apply leq_add.
    {
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
      rewrite addn_minr leq_min; apply/andP; split.
      {
        apply leq_add; apply LTserv;
        [specialize (INboth j_lst) | specialize (INboth j_fst)];
        rewrite INboth in_cons mem_rcons in_cons; apply/or3P;
        [by apply Or32 | by apply Or31].
      }
      {
        move: sorted; rewrite rcons_path; move => /andP sorted; des.
        
        admit.
        (*rewrite addnBA. rewrite addnBA. rewrite [task_cost _ + _]addnC.
        rewrite -addnBA. rewrite subnn addn0.
        admit.*) 
      }
    }
  }
Qed.

 (*
            have tmp := (Build_job (task_cost tsk) (task_deadline tsk) tsk).
            have bla := job_properties j; des.
            have bla2 := task_properties tsk; des.
            exploit tmp. 
              by repeat (split; try red); ins; try apply leqnn.
            intro j_tmp.
            Print Build_schedule_data. 
            ins.
            have j_tmp2 := j_tmp (job_properties j).
            Check job_properties j.
            Check (j_tmp).
            have j_tmp := 
            Print schedule.
            have PROP := sched_properties sched; des.
            apply RESP0 in ARRj; ins;
               last by destruct (task_eq_dec (job_task j) tsk).
            unfold completed in ARRj.
            apply leq_trans with (n := job_cost j).
            have PROP := job_properties j; des.          
            specialize (RESP1 true). JOB) *)

(*Lemma carried_in_unique :
  forall ts sched (ARRts: ts_arrival_sequence ts sched)
         (RESTR: restricted_deadline_model ts)
         tsk (IN: tsk \in ts) j (JOB: job_task j = tsk)
         arr (ARRj: arrives_at sched j arr)
         (SCHED: task_misses_no_deadlines sched ts tsk),
    let released_jobs := prev_arrivals sched (arr + job_deadline j) in
      (exists j_in, << CARRY: carried_in sched tsk arr j_in >> /\
                    << FILTER: filter (carried_in sched tsk arr) released_jobs = [::j_in] >>) \/
      << FILTER: filter (carried_in sched tsk arr) released_jobs = nil >>.
Proof.
Admitted.

Lemma carried_out_unique :
  forall ts sched (ARRts: ts_arrival_sequence ts sched)
         (RESTR: restricted_deadline_model ts)
         tsk (IN: tsk \in ts) j (JOB: job_task j = tsk)
         arr (ARRj: arrives_at sched j arr)
         (SCHED: task_misses_no_deadlines sched ts tsk),
  let released_jobs := prev_arrivals sched (arr + job_deadline j) in
    (exists j_out, << CARRY: carried_out sched tsk arr (arr + job_deadline j) j_out >> /\
                   << FILTER: filter (carried_out sched tsk arr (arr + job_deadline j))
                                released_jobs = [::j_out] >>) \/
    << FILTER: filter (carried_out sched tsk arr (arr + job_deadline j))
                 released_jobs = nil >>.
Proof.
Admitted.

Lemma workload_bound :
  forall ts sched (ARRts: ts_arrival_sequence ts sched)
         hp cpumap num_cpus (MULT: ident_mp num_cpus hp cpumap sched) 
         (RESTR: restricted_deadline_model ts)
         tsk (IN: tsk \in ts) j (JOB: job_task j = tsk)
         arr_j (ARRj: arrives_at sched j arr_j)
         (SCHED: task_misses_no_deadlines sched ts tsk)
         R_tsk (RESP: task_response_time_ub tsk ts R_tsk),
    (workload sched ts tsk arr_j (arr_j + job_deadline j)) <= W tsk R_tsk (job_deadline j).
Proof.
  unfold workload; ins.
  remember (prev_arrivals sched (arr_j + job_deadline j)) as released_jobs.
  rewrite (bigID (carried_out sched tsk arr_j (arr_j + job_deadline j))); simpl.
  apply leq_add.
  {
    rewrite -> eq_bigl with (P2 := fun x => carried_out sched tsk arr_j (arr_j + job_deadline j) x);
      last (
        by unfold ssrfun.eqfun, carried_out, job_of; ins;
        rewrite andb_idl //; move/and3P => CARRYjob; destruct CARRYjob).
    generalize SCHED; apply carried_out_unique with (j := j) (arr := arr_j) in SCHED; des; ins;
    rewrite <- Heqreleased_jobs in *;
    [rewrite -big_filter FILTER big_cons big_nil addn0 | by rewrite -big_filter FILTER big_nil //].

    rewrite leq_min; apply/andP; split.
    { 
      move: CARRY => /and3P CARRY; destruct CARRY as [JOB_out _ _].
      move: JOB_out => /eqP JOB_out; rewrite -JOB_out.
      have PROP := job_properties j_out; des.
      apply leq_trans with (n := job_cost j_out); [|by ins].
      by apply service_interval_max_cost; [by unfold ident_mp in *; des].
    }
    {
      move: CARRY => /and3P CARRY; destruct CARRY as [_ ARRout _]; unfold arrived_between in *.
      move: ARRout => /exists_inPQ_nat ARRout. destruct ARRout as [arr_out [LTout [GEout _]]].
      unfold service_during.
      assert (SUM: \sum_(arr_j <= t < arr_j + job_deadline j) service_at sched j_out t =
                   \sum_(arr_j <= t < arr_out) service_at sched j_out t + 
                   \sum_(arr_out <= t < arr_j + job_deadline j) service_at sched j_out t). admit.
      rewrite SUM.
      assert (ZERO: \sum_(arr_j <= t < arr_out) service_at sched j_out t = 0).  admit.
      rewrite ZERO add0n.
      apply leq_trans with (n := \sum_(arr_out <= t < arr_j + job_deadline j) 1).
        by apply leq_sum; unfold ident_mp in *; des; ins; rewrite mp_max_service.
      rewrite big_const_nat iter_addn addn0 mulnC muln1.
      rewrite addnC -subnBA //.
      
      (* Prove that service of t_0 + delta - arrival time of j_out <= (delta + R_k - e_k) % p_k *) 

      generalize SCHED; apply carried_in_unique with (j := j) (arr := arr_j) in SCHED; des; ins;
      rewrite <- Heqreleased_jobs in *.
      move: CARRY => /and3P CARRY; destruct CARRY as [_ ARRin _]; unfold arrived_before in *.
      move: ARRin => /exists_inP_nat ARRin; destruct ARRin as [arr_in [LTin ARRin]].

      assert (EXk: arr_out >= arr_in + div_floor (arr_out - arr_in) (task_period tsk)). admit.
      rewrite EXk.
      admit. admit.
    }
  }
  {
    rewrite big_seq_cond.
    apply leq_trans with
    (n := \sum_(i <- released_jobs | [&& (i \in released_jobs),
          job_of tsk i & ~~ carried_out sched tsk arr_j
                             (arr_j + job_deadline j) i]) task_cost tsk).
    {
      apply leq_sum; unfold job_of; intros j_i.
      move/and3P => INj_i; destruct INj_i.
      unfold beq_task in *; destruct task_eq_dec as [JOBi|]; ins.
      have PROP := job_properties j_i; des.
      apply leq_trans with (n := job_cost j_i); [|by rewrite -JOBi].
      apply service_interval_max_cost.
      by unfold ident_mp in MULT; des.
    }
    {
      rewrite big_const_seq iter_addn addn0 mulnC.
      rewrite leq_mul2r.
      apply/orP; right.
      unfold max_jobs.
      (* Prove that number of jobs minus carried-out <= n_k *)
      admit.
    }
  }
Qed.
*)
End WorkloadBound.