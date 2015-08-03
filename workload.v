Require Import Classical Vbase job task schedule task_arrival response_time platform
        schedulability divround helper priority identmp helper
        ssreflect ssrbool eqtype ssrnat seq div fintype bigop path ssromega.

Section WorkloadBound.
  
(* Workload is defined as the total service received by jobs of
   a specific task in the interval [t,t'). *)
Definition workload (sched: schedule) (ts: taskset) (tsk: sporadic_task) (t t': time) :=
  \sum_(j <- prev_arrivals sched t' | job_task j == tsk) (service_during sched j t t').

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

(*Lemma max_jobs_bound :
  forall tsk delta R_tsk (GT: R_tsk >= task_cost tsk),
    (max_jobs tsk R_tsk delta).+1 >= div_ceil (delta + R_tsk) (task_period tsk).
Proof.
  unfold max_jobs, div_floor, div_ceil; ins.
  have PROP := task_properties tsk; des.
  destruct (task_period tsk %| (delta + R_tsk)) eqn:DIV.
  {
    move: DIV => /dvdnP DIV; des.
    rewrite DIV mulnK //.
    destruct k; first by rewrite mul0n sub0n div0n.
    {
      apply leq_trans with (n := ((k.+1 * task_period tsk - task_period tsk) %/ task_period tsk).+1).
        by rewrite mulSn addnC -addnBA // subnn addn0 mulnK.
        by rewrite ltnS leq_div2r // leq_sub2l //.
    }
  }
  {
    have bla := geq_divBl.
    specialize (bla (delta + R_tsk) (task_cost tsk) (task_period tsk)).
  }

  
    by rewrite leq_div2r // -addnBA // leq_addr.

Qed.*)

Lemma max_num_jobs_ceil :
  forall ts sched (ARRts: ts_arrival_sequence ts sched)
         (RESTR: restricted_deadline_model ts) tsk (IN: tsk \in ts)
         (SCHED: task_misses_no_deadlines sched ts tsk) t1 t2,
    let released_jobs := filter (fun x => (job_task x == tsk) &&
                                (service_during sched x t1 t2 != 0)) (prev_arrivals sched t2) in  
    size released_jobs <= div_ceil (t2 - t1) (task_period tsk).
Proof.
(*
  ins; unfold div_ceil in *.
  set released_jobs := filter (fun x => (job_task x == tsk) &&
                                (service_during sched x t1 t2 != 0)) (prev_arrivals sched t2).
  have PROP := task_properties tsk; des.

  (* Order the sequence of released_jobs by arrival time, so that
     we identify easily the first and last jobs. *)
  set order := fun x y => job_arrival x <= job_arrival y.
  set sorted_jobs := (sort order released_jobs).
  assert (SORT: sorted order sorted_jobs);
      first by apply sort_sorted; unfold total, order; ins; apply leq_total.

  (* State that the sorted list has the same size as the old one *)
  rewrite <- perm_eq_size with (s1 := sorted_jobs); last by rewrite (perm_sort order).

  (* Create some random job to use as default of nth *)
  assert(VALIDj: << X: 0 < task_cost tsk >> /\
                 << X: task_cost tsk <= task_deadline tsk >> /\
                 << X: 0 < task_deadline tsk >> /\
                 << X: task_cost tsk <= task_cost tsk /\ task_deadline tsk = task_deadline tsk >>).
    by repeat split; try apply leqnn; ins.
  set j := Build_job 0 (task_cost tsk) (task_deadline tsk) tsk VALIDj.
    
  (* Remember that the jobs are ordered by arrival *)
  assert (ALL: forall i (LTsort: i < (size sorted_jobs).-1),
                 order (nth j sorted_jobs i) (nth j sorted_jobs i.+1)).
    by destruct sorted_jobs; [by ins| by apply/pathP; apply SORT].
 
  (* Remember that both sequences have the same set of elements *)
  assert (INboth: forall x, (x \in released_jobs) = (x \in sorted_jobs)).
    by apply perm_eq_mem; rewrite -(perm_sort order).


  set n := size sorted_jobs.
  set j_fst := (nth j sorted_jobs 0).
  set j_lst := (nth j sorted_jobs n.+1).
  
  destruct (task_period tsk %| (t2 - t1)) eqn:DIV.
  {
    rewrite leq_divRL //.
    apply leq_trans with (n := job_arrival j_lst - (job_arrival j_fst + task_period tsk)).
    {
      rewrite subnDA.
      apply leq_trans with (n := n.-1*task_period tsk - task_period tsk).


      apply subh3. last first. addnBA. subh3. -subh1. addnBA. subnBA. subh1. -addnBA.
    }
    {
      admit.
    }
  }
    
  (* Index the sequence *)
  rewrite -sum1_size (big_nth j).
  set n := size sorted_jobs.
  destruct n; first by rewrite big_geq.

  rewrite big_nat_recl.
  (* Take first and last elements out of the sum *) 
  rewrite [nth]lock big_nat_recl // big_nat_recr // /= -lock.
  
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
    move: DIV => /dvdnP DIV; des.
    rewrite DIV.

    ; [|apply leqW]; rewrite leq_divRL //.
  {
    
  }
    
  assert (LTsize: size released_jobs * task_period tsk <= t2 - t1).
  {
    rewrite -sum1_size.
    apply leq_trans with (n := t2 - (t1 + task_period tsk)); last by apply leq_sub2l, leq_addr.
    

    admit.
  }

  by destruct (task_period tsk %| (t2 - t1)) eqn:DIV; [|apply leqW]; rewrite leq_divRL //.*)
Admitted.

Theorem workload_bound :
  forall ts sched (SPO: sporadic_task_model ts sched)
         hp (VALIDhp: valid_jldp_policy hp)
         cpumap num_cpus (MULT: ident_mp num_cpus hp cpumap sched)
         (RESTR: restricted_deadline_model ts)
         tsk (IN: tsk \in ts) j (JOB: job_task j = tsk)
         arr_j (ARRj: arrives_at sched j arr_j)
         (NOMISS: task_misses_no_deadlines sched ts tsk)
         R_tsk (RESP: forall mapped, response_time_ub (ident_mp num_cpus hp mapped) ts tsk R_tsk),
    (workload sched ts tsk arr_j (arr_j + job_deadline j)) <= W tsk R_tsk (job_deadline j).
Proof.
  unfold sporadic_task_model, workload, W; ins; des.

  (* Simplify names *)
  set t1 := arr_j.
  set t2 := arr_j + job_deadline j.
  set n_k := max_jobs tsk R_tsk (job_deadline j).

  (* Remember the maximum number of jobs that contribute to the workload *)
  (*have CEIL := max_num_jobs_ceil ts sched ARRts RESTR tsk IN NOMISS t1 t2;
  simpl in *.*)

  (* Use a simpler name for the set of jobs that we are interested in *)
  set released_jobs :=
    filter (fun x => (job_task x == tsk) && (service_during sched x t1 t2 != 0))
                    (prev_arrivals sched t2). (*; fold released_jobs in CEIL.*)
  
  (* Remove the elements that we don't care about from the sum *)
  assert (SIMPL:
    \sum_(i <- prev_arrivals sched t2 | job_task i == tsk)
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

  assert (EQdelta: t2 - t1 = job_deadline j).
    by unfold t1,t2; rewrite addnC -addnBA // subnn addn0.
    
  (* Now we begin the proof. *)

    (* Let num_jobs = (size released_jobs). Then, either (1) num_jobs <= n_k, or (2) num_jobs > n_k. *)
  (*set num_jobs := size released_jobs.*) 


  (*destruct (num_jobs <= n_k) eqn:NUM.
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
    (*assert (EQnum: num_jobs == n_k.+1).
    {
      (*
      apply negbT in NUM; rewrite -ltnNge in NUM.
      rewrite eqn_leq; apply/andP; split; last by ins.
      apply leq_trans with (n := div_ceil (job_deadline j) (task_period tsk));
      [by rewrite -EQdelta | by apply max_jobs_bound].*) admit.
    } clear NUM.*)
    apply negbT in NUM; rewrite -ltnNge in NUM.

   *)
  
    (* Order the sequence of released_jobs by arrival time, so that
       we identify easily the first and last jobs. *)
    set order := fun x y => job_arrival x <= job_arrival y.
    set sorted_jobs := (sort order released_jobs).
    assert (SORT: sorted order sorted_jobs);
      first by apply sort_sorted; unfold total, order; ins; apply leq_total.
    rewrite (eq_big_perm sorted_jobs) /=; last by rewrite -(perm_sort order).

 
    (* State that the sorted list has the same size as the old one *)
    (*set num_jobs := size sorted_jobs.*)                 
    (*assert (EQ: num_jobs = num_jobs_s).
      by apply perm_eq_size; rewrite -(perm_sort order).*)
    (*fold num_jobs in CEIL;*) (*rewrite -> EQ in *; clear EQ num_jobs.*)
      (*rename num_jobs_s into num_jobs; simpl in *.*)
      

    (* Remember that both sequences have the same set of elements *)
    assert (INboth: forall x, (x \in released_jobs) = (x \in sorted_jobs)).
      by apply perm_eq_mem; rewrite -(perm_sort order).

    (* Index the sequence *)
    rewrite (big_nth j); set num_jobs := size sorted_jobs.


    destruct (size sorted_jobs) eqn:SIZE; first by rewrite big_geq //.

    exploit (mem_nth j); last intros FST.
      by instantiate (1:= sorted_jobs); instantiate (1 := 0); rewrite SIZE.
    move: FST; rewrite -INboth mem_filter; move => /andP FST; des.
    move: FST => /andP FST; des; move: FST => /eqP FST.
    rename FST0 into FSTin, FST into FSTtask, FST1 into FSTserv.
    
    destruct n.
    {
      destruct n_k.
      {
        rewrite 2!mul0n addn0 subn0 big_nat_recl // big_geq // addn0.
        rewrite leq_min; apply/andP; split.
        {
          apply leq_trans with (n := job_cost (nth j sorted_jobs 0)).
          apply service_interval_max_cost; first by unfold ident_mp in MULT; des; ins.
          by rewrite -FSTtask; have PROP := job_properties (nth j sorted_jobs 0); des.
        }
        {
        rewrite -addnBA; last by ins.
        rewrite -[service_during _ _ _ _]addn0.
        apply leq_add; last by ins.
        unfold service_during; apply leq_trans with (n := \sum_(t1 <= t < t2) 1).
          by apply leq_sum; intros i _; unfold ident_mp in MULT; des; apply mp_max_service.
          by rewrite big_const_nat iter_addn mul1n addn0 EQdelta.
        }
      }
      
      rewrite big_nat_recl // big_geq // addn0 -[service_during _ _ _ _]add0n.  
      apply leq_add; first by ins.
      apply leq_trans with (n := task_cost tsk);
        last by rewrite -{1}[task_cost _]mul1n leq_pmul2r; [| have PROP := task_properties tsk; des].
      apply leq_trans with (n := job_cost (nth j sorted_jobs 0)).
      apply service_interval_max_cost; first by unfold ident_mp in MULT; des; ins.
      by rewrite -FSTtask; have PROP := job_properties (nth j sorted_jobs 0); des.
    }
    {
      unfold num_jobs in *; clear num_jobs.
      (*rewrite subn2 in NUM; simpl in NUM.*)

    (* Show that the inequality holds if there's a single element in the list. *)
    (*move: EQnum => /eqP EQnum; rewrite EQnum; unfold num_jobs in EQnum.*)
    (*destruct num_jobs eqn:SIZE; first by rewrite ltn0 in NUM.
    destruct n.
    {
      rewrite big_nat_recl // big_geq // addn0.
      unfold n_k, max_jobs, div_floor in *.
      rewrite ltnS leqn0 in NUM; move: NUM => /eqP NUM; rewrite -> NUM in *.
      rewrite 2!mul0n subn0 addn0.
      have DIV := divn_eq (job_deadline j + R_tsk - task_cost tsk) (task_period tsk).
      rewrite NUM mul0n add0n in DIV.
      have MOD_ := ltn_pmod.
      exploit (MOD_ (job_deadline j + R_tsk - task_cost tsk) (task_period tsk));
        [by have PROP := task_properties tsk; des | intro MOD; clear MOD_].
      rewrite -DIV in MOD; clear DIV.
      
      exploit (mem_nth j); last intros NTH.
        by instantiate (1:= sorted_jobs); instantiate (1 := 0); by rewrite -SIZE.
      move: NTH; rewrite -INboth mem_filter; move => /andP NTH; des.
      move: NTH => /andP NTH; des.
      rewrite leq_min; apply/andP; split.
      {
        apply leq_trans with (n := job_cost (nth j sorted_jobs 0)).
        apply service_interval_max_cost; first by unfold ident_mp in MULT; des; ins.
        move: NTH => /eqP NTH. rewrite -NTH.
        by have PROP := job_properties (nth j sorted_jobs 0); des.
      }
      {
        rewrite -addnBA; last by ins.
        rewrite -[service_during _ _ _ _]addn0.
        apply leq_add; last by ins.
        unfold service_during; apply leq_trans with (n := \sum_(t1 <= t < t2) 1).
          by apply leq_sum; intros i _; unfold ident_mp in MULT; des; apply mp_max_service.
          by rewrite big_const_nat iter_addn mul1n addn0 EQdelta.
      }
    }

    destruct n_k. admit. destruct n_k. admit. *)

    
    (*destruct n_k.
    {
      rewrite big_nat_recl // big_geq // 2!mul0n subn0 2!addn0.
      rewrite leq_min; apply/andP; split; first by apply LTserv; rewrite INboth mem_nth // EQnum.
      rewrite -addnBA // -[service_during sched _ _ _]addn0.
      apply leq_add; last by ins.
      unfold service_during; apply leq_trans with (n := \sum_(t1 <= t < t2) 1).
      apply leq_sum; ins; first by unfold ident_mp in MULT; des; apply mp_max_service.
      by rewrite big_const_nat iter_addn mul1n addn0 -EQdelta.
    }*)

    (* Take first and last elements out of the sum *) 
    rewrite [nth]lock big_nat_recl // big_nat_recr // /= -lock.

    rewrite addnA addnC addnA.

    (*(* Move one (task_cost tsk) term inside the min *)
    rewrite [_ * task_cost _]mulSn [_ + (task_cost _ + _)]addnA addn_minl.
    rewrite addnA -addnC addnA.*)

    assert (NK: n_k >= (size sorted_jobs).-2). admit.
    rewrite SIZE in NK; simpl in NK.

    (*destruct (num_jobs <= n_k) eqn:LE.
    {
      admit.
    }
    apply negbT in LE; rewrite -ltnNge in LE.
    destruct (num_jobs == n_k.+1). admit.*)

    
    (* Bound the service of the middle jobs *)
    apply leq_add; last first.
    {
      apply leq_trans with (n := n * task_cost tsk);
        last by rewrite leq_pmul2r; [| have PROP := task_properties tsk; des].
      apply leq_trans with (n := \sum_(0 <= i < n) task_cost tsk);
        last by rewrite big_const_nat iter_addn addn0 mulnC subn0.
      rewrite big_nat_cond [\sum_(0 <= i < n) task_cost _]big_nat_cond.
      apply leq_sum; intros i; rewrite andbT; move => /andP LT; des.
      by apply LTserv; rewrite INboth mem_nth // SIZE ltnS leqW.
    }
    {
        set j_fst := (nth j sorted_jobs 0).
        set j_lst := (nth j sorted_jobs n.+1).
                     
        (* First let's infer some facts about how the events are ordered in the timeline *)
        assert (INfst: j_fst \in released_jobs).
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
          apply (mem_nth j) in LTsize; rewrite -INboth in LTsize.
          rewrite -/released_jobs mem_filter in LTsize.  
          move: LTsize => /andP xxx; des; move: xxx xxx0 => /andP xxx INlst; des.
          rename xxx0 into SERV; clear xxx.
          unfold service_during in SERV; move: SERV => /negP SERV; apply SERV.
          by rewrite sum_service_before_arrival.
        }

        (*assert (NK_LE_DELTA: n.+1 * task_period tsk <= job_deadline j).
        {
          unfold numdiv_ceil in *; rewrite EQnum in CEIL; rewrite -> EQdelta in *.
          have PROP := task_properties tsk; des.
          destruct (task_period tsk %| job_deadline j) eqn:DIV.
            by rewrite -leq_divRL; [by apply ltnW | by ins].
            by rewrite ltnS leq_divRL in CEIL.
        }*)

        (* Remember that the jobs are ordered by arrival *)
        assert (ALL: forall i (LTsort: i < (size sorted_jobs).-1),
                   order (nth j sorted_jobs i) (nth j sorted_jobs i.+1)).
          by destruct sorted_jobs; [by ins| by apply/pathP; apply SORT].

        
        apply leq_trans with (n := (job_arrival j_fst  + R_tsk - t1) +
                                   (t2 - job_arrival j_lst)).
        {
          rewrite addnC; apply leq_add; unfold service_during.
          {
            rewrite -[_ + _ - _]mul1n -[1*_]addn0 -iter_addn -big_const_nat.
            apply leq_trans with (n := \sum_(t1 <= t < job_arrival j_fst + R_tsk)
                                         service_at sched j_fst t);
              last by apply leq_sum; unfold ident_mp in MULT; des; ins; apply mp_max_service.
            destruct (job_arrival j_fst + R_tsk <= t2) eqn:LEt2; last first.
            {
              apply negbT in LEt2; rewrite -ltnNge in LEt2.
              rewrite -> big_cat_nat with (n := t2) (p := job_arrival j_fst + R_tsk);
                by try apply leq_addr; try apply ltnW.
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
              apply leq_trans with (n := \sum_(job_arrival j_lst <= t < t2) service_at sched j_lst t).
              rewrite -> big_cat_nat with (m := job_arrival j_lst) (n := t1);
                [by apply leq_addl | by ins | by unfold t1, t2; apply leq_addr].
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

        rewrite addnBA; last by apply ltnW.
        rewrite subh1 // -addnBA; last by apply leq_addr.
        rewrite addnC [job_arrival _ + _]addnC.
        unfold t1, t2; rewrite [arr_j + _]addnC -[_ + arr_j - _]addnBA // subnn addn0.
        rewrite addnA -subnBA; last first.
        {
          unfold j_fst, j_lst. rewrite -[n.+1]add0n.
          apply prev_le_next; [by ins | by rewrite SIZE add0n ltnSn].
        }

        apply leq_trans with (n := job_deadline j + R_tsk - (size sorted_jobs).-1*(task_period tsk)).
        {
          apply leq_sub2l.
          assert (EQnk: n.+1=(size sorted_jobs).-1); first by rewrite SIZE. 
          unfold j_fst, j_lst; rewrite EQnk telescoping_sum; last by ins.
          rewrite -[_ * _ tsk]addn0 mulnC -iter_addn -{1}[_.-1]subn0 -big_const_nat. 
          rewrite big_nat_cond [\sum_(0 <= i < _)(_-_)]big_nat_cond.
          apply leq_sum; intros i; rewrite andbT; move => /andP LT; des.
          {
            (* To simplify, call the jobs 'cur' and 'next' *)
            set cur := nth j sorted_jobs i.
            set next := nth j sorted_jobs i.+1.
            clear LT EQdelta LTserv NEXT j_fst j_lst INfst INfst0 INfst1 AFTERt1 BEFOREt2.

            (* Show that cur arrives earlier than next *)
            assert (ARRle: job_arrival cur <= job_arrival next).
            {
              unfold cur, next; rewrite -addn1; apply prev_le_next; first by ins.
              by apply leq_trans with (n := i.+1); try rewrite addn1.
            }
            
            (* Show that both cur and next are in the arrival sequence *)
            assert (INnth: cur \in released_jobs /\ next \in released_jobs).
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
               Since we don't know much about the list, except that it's sorted, we must
               prove that it doesn't contain duplicates. *)
            unfold t2 in ARRle.
            unfold interarrival_times in *; des.
            assert (CUR_LE_NEXT: arr_cur + task_period (job_task cur) <= arr_next).
            {
              apply INTER with (j' := next); try by ins.
              unfold cur, next, not; intro EQ; move: EQ => /eqP EQ.
              rewrite nth_uniq in EQ; first by move: EQ => /eqP EQ; intuition.
                by apply ltn_trans with (n := (size sorted_jobs).-1); destruct sorted_jobs; ins.
                by destruct sorted_jobs; ins.
                by rewrite sort_uniq -/released_jobs filter_uniq //; apply uniq_prev_arrivals.
                by move: INnth INnth0 => /eqP INnth /eqP INnth0; rewrite INnth INnth0.  
            }
            by rewrite subh3 // addnC; move: INnth => /eqP INnth; rewrite -INnth.
          }
        }
        
        (*assert (EQnk: n_k = n). admit.*)
        rewrite leq_min; apply/andP; split.
        {
          rewrite leq_subLR [_ + task_cost _]addnC -leq_subLR.
          rewrite ltnW // -ltn_divLR; last by have PROP := task_properties tsk; des.
          by rewrite SIZE /= -EQnk; unfold n_k, max_jobs, div_floor.
        }
        {
          rewrite -subnDA; apply leq_sub2l.
          rewrite SIZE /= -addn1 -EQnk addnC mulnDl mul1n.
          rewrite leq_add2l; last by have PROP := task_properties tsk; des. 
        }
      }
    }
Qed.  

        (* Show that both cur and next are in the arrival sequence *)
        assert (INnth: cur \in released_jobs /\ next \in released_jobs).
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
               Since we don't know much about the list, except that it's sorted, we must
               prove that it doesn't contain duplicates. *)
            unfold t2 in ARRle.
            unfold interarrival_times in *; des.
            assert (CUR_LE_NEXT: arr_cur + task_period (job_task cur) <= arr_next).
            {
              apply INTER with (j' := next); try by ins.
              unfold cur, next, not; intro EQ; move: EQ => /eqP EQ.
              rewrite nth_uniq in EQ; first by move: EQ => /eqP EQ; intuition.
                by apply ltn_trans with (n := (size sorted_jobs).-1); destruct sorted_jobs; ins.
                by destruct sorted_jobs; ins.
                by rewrite sort_uniq -/released_jobs filter_uniq //; apply uniq_prev_arrivals.
                by move: INnth INnth0 => /eqP INnth /eqP INnth0; rewrite INnth INnth0.  
            }
            by rewrite subh3 // addnC; move: INnth => /eqP INnth; rewrite -INnth.
          }














        
        rewrite -addn1.
        rewrite [n.+1 + 1]addnC. rewrite mulnDl.
        
        rewrite leq_min; apply/andP; split.
        {
          unfold n_k, max_jobs, div_floor in NUM.
        }
        apply leq_add; apply LTserv; rewrite INboth mem_nth. // SIZE.
      {


        (* Now we continue the proof, showing that the service can be bounded
           using the arrival times of the first and last jobs. *)
        apply leq_trans with (n := (job_arrival j_fst  + R_tsk - t1) +
                                   (t2 - job_arrival j_lst)).
        {
          rewrite addnC; apply leq_add; unfold service_during.
          {
            rewrite -[_ + _ - _]mul1n -[1*_]addn0 -iter_addn -big_const_nat.
            apply leq_trans with (n := \sum_(t1 <= t < job_arrival j_fst + R_tsk)
                                         service_at sched j_fst t);
              last by apply leq_sum; unfold ident_mp in MULT; des; ins; apply mp_max_service.
            destruct (job_arrival j_fst + R_tsk <= t2) eqn:LEt2; last first.
            {
              apply negbT in LEt2; rewrite -ltnNge in LEt2.
              rewrite -> big_cat_nat with (n := t2) (p := job_arrival j_fst + R_tsk);
                by try apply leq_addr; try apply ltnW.
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
              apply leq_trans with (n := \sum_(job_arrival j_lst <= t < t2) service_at sched j_lst t).
              rewrite -> big_cat_nat with (m := job_arrival j_lst) (n := t1);
                [by apply leq_addl | by ins | by unfold t1, t2; apply leq_addr].
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
        {
          (* Now we show that the expression with the arrival times is no larger
             than the workload bound for j_fst and j_lst (based on n_k).
             For that, we need to rearrange the formulas. *)
          rewrite [_ - _ + task_cost _]subh1;
            last by rewrite -addnBA // -[_*_]addn0; apply leq_add.
          rewrite [_ - _ + task_cost _]subh1; last first.
          {
            rewrite -[task_cost _]addn0; apply leq_add; last by ins.
            have PROP := job_properties j; des; rewrite job_params0 JOB.
            by have PROP2 := task_properties tsk; des.
          }
          rewrite -[_ + _ - task_cost _]addnBA // subnn addn0.
          rewrite addnC addnBA; last by ins.
          rewrite leq_subLR [_ + R_tsk]addnC.
          rewrite subh1; last by apply ltnW.
          rewrite addnA addnBA; last by rewrite -[_*_]addn0; apply leq_add.
          rewrite -subnBA; last first.
          {
            unfold j_fst, j_lst; rewrite -[_.+1]add0n; apply prev_le_next; first by ins.
            by rewrite add0n EQnum ltnSn.
          }
          rewrite addnA; unfold t1, t2; apply leq_sub2l.
      
          (* Final step: derive the minimum separation between the first
             and last jobs using the period and number of middle jobs. *)
          assert (EQnk: n_k.+1=(size sorted_jobs).-1); [by destruct sorted_jobs;[ins|rewrite EQnum]|].
          unfold j_fst, j_lst; rewrite EQnk telescoping_sum; last by ins.
          rewrite -[_ * _ tsk]addn0 mulnC -iter_addn -{1}[_.-1]subn0 -big_const_nat. 
          rewrite big_nat_cond [\sum_(0 <= i < _)(_-_)]big_nat_cond.
          apply leq_sum; intros i; rewrite andbT; move => /andP LT; des.
          {
            (* To simplify, call the jobs 'cur' and 'next' *)
            set cur := nth j sorted_jobs i.
            set next := nth j sorted_jobs i.+1.
            clear LT EQdelta CEIL LTserv NEXT j_fst j_lst INfst INfst0 INfst1 AFTERt1 BEFOREt2.

            (* Show that cur arrives earlier than next *)
            assert (ARRle: job_arrival cur <= job_arrival next).
            {
              unfold cur, next; rewrite -addn1; apply prev_le_next; first by ins.
              by apply leq_trans with (n := i.+1); try rewrite addn1.
            }
            
            (* Show that both cur and next are in the arrival sequence *)
            assert (INnth: cur \in released_jobs /\ next \in released_jobs).
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
               Since we don't know much about the list, except that it's sorted, we must
               prove that it doesn't contain duplicates. *)
            unfold t2 in ARRle.
            unfold interarrival_times in *; des.
            assert (CUR_LE_NEXT: arr_cur + task_period (job_task cur) <= arr_next).
            {
              apply INTER with (j' := next); try by ins.
              unfold cur, next, not; intro EQ; move: EQ => /eqP EQ.
              rewrite nth_uniq in EQ; first by move: EQ => /eqP EQ; intuition.
                by apply ltn_trans with (n := (size sorted_jobs).-1); destruct sorted_jobs; ins.
                by destruct sorted_jobs; ins.
                by rewrite sort_uniq -/released_jobs filter_uniq //; apply uniq_prev_arrivals.
                by move: INnth INnth0 => /eqP INnth /eqP INnth0; rewrite INnth INnth0.  
            }
            by rewrite subh3 // addnC; move: INnth => /eqP INnth; rewrite -INnth.
          }
        }
      }
    }
  }
Qed.

End WorkloadBound.