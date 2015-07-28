Require Import Vbase task job schedule priority platform task_arrival
        response_time ssreflect ssrbool eqtype seq ssrnat bigop helper.

Definition job_mapping := job -> processor_id -> time -> bool.

(* Identical multiprocessor platform *)
Definition ident_mp (num_cpus: nat) (hp: sched_job_hp_relation) (mapped: job_mapping) (sched: schedule) :=
  (* The mapping has a finite positive number of cpus: [0, num_cpus) *)
  << mp_cpus_nonzero: num_cpus > 0 >> /\
  << mp_num_cpus: forall j cpu t, mapped j cpu t -> cpu < num_cpus >> /\

  (* Job is scheduled iff it is mapped to some processor*)
  << mp_mapping: forall j t, scheduled sched j t <-> exists cpu, mapped j cpu t >> /\

  (* Non-parallelism restrictions (mapping must be an injective function) *)
  << mp_mapping_fun: forall j cpu cpu' t, mapped j cpu t /\ mapped j cpu' t -> cpu = cpu' >> /\
  << mp_mapping_inj: forall j j' cpu t, mapped j cpu t /\ mapped j' cpu t -> j = j'>> /\
  
  (* A job receives at most 1 unit of service *)
  << mp_max_service: forall j t, service_at sched j t <= 1 >> /\

  (* Global scheduling invariant *)
  << mp_invariant: forall jlow t (ARRIVED: arrived sched jlow t),
    backlogged sched jlow t <->
      (exists (j0: job), earlier_job sched j0 jlow /\ pending sched j0 t) \/
      (forall cpu (MAXcpu: cpu < num_cpus),
       exists jhigh, hp sched t jhigh jlow /\ mapped jhigh cpu t) >>.

(* TODO/Observations *)
(* 1) Note that the scheduling invariant only applies to jobs that
      have arrived in the schedule, thus the need for (ARRIVED: ...).
      If all processors are occupied by higher-priority
      jobs, it doesn't mean that a random job jlow (not part of the
      task set) is backlogged.
 *)

Definition my_service_at (my_j j: job) (t: time) :=
  if my_j == j then
    (if t < task_cost (job_task j) then 1 else 0)
  else 0.

Definition my_arr_seq (my_j: job) (t: nat) :=
  if (t == 0) then [::my_j] else [::].

Lemma rt_geq_wcet_identmp :
  forall ts tsk R_tsk num_cpus hp
         (GTcpus: num_cpus > 0)
         (VALIDhp: valid_jldp_policy hp)
         (RESP: forall mapped,
            response_time_ub (ident_mp num_cpus hp mapped) ts tsk R_tsk),
    R_tsk >= task_cost tsk.  
Proof.
  unfold response_time_ub; ins; des.
  have PROP := task_properties tsk; des.

  assert (VALIDj:  << X1: 0 < task_cost tsk >> /\
                   << X2: task_cost tsk <= task_deadline tsk >> /\
                   << X3: 0 < task_deadline tsk >> /\
                   << X4: task_cost tsk <= task_cost tsk >> /\
                   << X5: task_deadline tsk = task_deadline tsk >> ).
    by repeat split; ins; try apply leqnn; clear tmp_job; rename x0 into j.    
  set j := Build_job 0 (task_cost tsk) (task_deadline tsk) tsk VALIDj.

  assert (VALIDarr: << NOMULT: forall (j0 : job_eqType) (t1 t2 : time),
                         j0 \in my_arr_seq j t1 -> j0 \in my_arr_seq j t2 -> t1 = t2 >> /\
                    << ARR_PARAMS: forall (j0 : job_eqType) (t : time),
                        j0 \in my_arr_seq j t -> job_arrival j0 = t >>).
  {
    split; red.
      by intros j0 t1 t2 ARR1 ARR2; unfold my_arr_seq in *; destruct t1, t2; ins.
      intros j0 t ARRj0; unfold my_arr_seq in *; destruct t; simpl in *.
        by move: ARRj0; rewrite mem_seq1; move => /eqP ARRj0; subst.
        by rewrite in_nil in ARRj0.
  }
  set arr := Build_arrival_sequence (my_arr_seq j) VALIDarr.

  assert (VALIDsched: (<< VALID0: forall (j0 : job) (t : time),
   scheduled {| service_at := my_service_at j; arr_list := arr |} j0 t ->
   arrived {| service_at := my_service_at j; arr_list := arr |} j0 t >> /\   
    << VALID1: forall (j0 : job) (t : nat) (t_comp : time),
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
      {
        assert (LT: t_comp < task_cost tsk).
          by apply leq_trans with (n := t.+1); [rewrite ltnS | ins].
        move: COMPLETED => /eqP COMPLETED; rewrite <- COMPLETED in *.
        assert (LTNN: t_comp < t_comp); last by rewrite ltnn in LTNN. 
        {
          apply leq_trans with (n := \sum_(0 <= t0 < t_comp)
                                      my_service_at j j t0); first by ins.
          apply leq_trans with (n := \sum_(0 <= t0 < t_comp) 1);
            last by rewrite big_const_nat iter_addn mul1n addn0 subn0.
          apply leq_sum; ins; unfold my_service_at; rewrite eq_refl.
          by destruct (i < task_cost (job_task j)); ins.
        }
      }
    }
  }
  
  set sched := Build_schedule (Build_schedule_data (my_service_at j) arr) VALIDsched.

  set my_cpumap : job_mapping :=
    (fun j' cpu t => [&& j == j', (cpu == 0) & service_at sched j t == 1]).
  
  assert (MULT: ident_mp num_cpus hp my_cpumap sched).
  {
    unfold ident_mp; repeat (split; try red); first by ins.
    {
      unfold my_cpumap; intros j0 cpu t; move => /and3P MAP.
      by destruct MAP as [_ EQ0 _]; move: EQ0 => /eqP EQ0; subst.
    }
    {
      unfold scheduled, my_cpumap; simpl; intros SCHED; exists 0; des.
      unfold my_service_at in *; destruct (j == j0) eqn:EQjj0;
      rewrite 2?eq_refl.
      apply/and3P; split; ins.
        by move: EQjj0 => /eqP EQjj0; subst j0; simpl in *; destruct (t < task_cost tsk).
        by move: SCHED => /eqP SCHED; intuition.
    }
    {
      unfold scheduled; intros MAP; des.
      move: MAP => /and3P MAP; destruct MAP as [EQjj0 _ SERV].
      move: EQjj0 SERV => /eqP EQjj0 /eqP SERV.
      by apply/eqP; unfold not; intro EQ; subst j0; intuition.
    }
    {
      unfold my_cpumap; intros j0 cpu cpu' t MAP; des.
      by move: MAP1 MAP3 => /eqP MAP1 /eqP MAP3; subst.
    }
    {
      unfold my_cpumap; intros j0 j' cpu t MAP; des.
      by move: MAP0 MAP => /eqP MAP0 /eqP MAP; subst j0.
    }
    {
      ins; unfold my_service_at.
      by destruct (j == j0); destruct (t < task_cost (job_task j0)); ins.
    }
    {
      move: ARRIVED; unfold arrived. move => /exists_inP_nat ARRIVED; des.
      unfold arrives_at in ARRIVED0; simpl in *; unfold my_arr_seq in *.
      destruct (x == 0); last by rewrite in_nil in ARRIVED0.
      rewrite mem_seq1 in ARRIVED0; move: ARRIVED0 => /eqP ARRIVED0; subst.
      unfold backlogged, pending; intros BACK.
      repeat (move: BACK => /andP BACK; des).
      unfold scheduled, arrived in BACK, BACK0.
      move: BACK => /exists_inP_nat => BACK; des; clear BACK2.
      simpl in BACK0; unfold my_service_at in BACK0.
      rewrite eq_refl negbK in BACK0.
      destruct (t < task_cost (job_task j)) eqn:LT;
        first by move: BACK0 => /eqP BACK0; intuition.
      clear BACK0; apply negbT in LT; rewrite -leqNgt in LT.
      unfold completed in BACK1.
      assert (EQ: service sched j t = job_cost j);
        last by move: BACK1; rewrite EQ; move => /eqP BACK1; intuition.
      {
        unfold service; simpl; unfold my_service_at; rewrite eq_refl; simpl.
        rewrite -> big_cat_nat with (n := (task_cost tsk)); ins.
        rewrite -> eq_big_nat with (F2 := (fun i => 1));
        last by intros i; move => /andP LTi; des; rewrite LTi0.
        {
          rewrite big_const_nat iter_addn subn0 addn0 mul1n.
          rewrite -> eq_big_nat with (F2 := (fun i => 0));
          first by rewrite big_const_nat iter_addn addn0 mul0n addn0.
          {
            intros i GT; move: GT => /andP => GT; des.
            destruct (i < task_cost tsk) eqn:LTi; last by ins.
            {
              rewrite leq_eqVlt in GT; move: GT => /orP GT; des.
              by move: GT => /eqP GT; subst; rewrite ltnn in LTi; ins.
              by apply ltn_trans with (m := i) in GT; [rewrite ltnn in GT|].
            }
          }
        }
      }
    }
    {
      intros OTHER; des.
      {
        unfold earlier_job in OTHER; des; unfold arrives_at in *.
        simpl in *. unfold my_arr_seq in *.
        assert (NOMULT' := NOMULT j0 arr1 arr2).
        destruct (arr1 == 0); last by rewrite in_nil in ARR1.
        destruct (arr2 == 0); last by rewrite in_nil in ARR2.
        rewrite mem_seq1 in ARR1; rewrite mem_seq1 in ARR2;
        rewrite mem_seq1 in NOMULT'.
        move: ARR1 ARR2 => /eqP ARR1 /eqP ARR2; subst j0 jlow.
        exploit NOMULT'; try apply/eqP; ins; subst.
        by rewrite ltnn in LT.
      }
      {
        move: ARRIVED; unfold arrived. move => /exists_inP_nat ARRIVED; des.
        unfold arrives_at in ARRIVED0; simpl in *; unfold my_arr_seq in *.
        destruct (x == 0); last by rewrite in_nil in ARRIVED0.
        rewrite mem_seq1 in ARRIVED0; move: ARRIVED0 =>/eqP ARRIVED0; subst.
        exploit OTHER; [by instantiate (1 := 0) | intros MAP; des].
        move: MAP0; unfold my_cpumap; move => /and3P MAP0.
        destruct MAP0 as [EQ _ SERV].
        move: EQ => /eqP EQ; subst jhigh.
        unfold valid_jldp_policy, ExtraRelations.irreflexive in *; des.
        by exfalso; apply (hpIrr sched t j).
      }
    }
  }       
          
  assert (ARRts: ts_arrival_sequence ts sched).
  {
    unfold ts_arrival_sequence; ins.
    unfold arrives_at, arr_list, arr, my_arr_seq in ARR; simpl in ARR.
    destruct (t == 0); last by rewrite in_nil in ARR.
      move: ARR; rewrite mem_seq1; move => /eqP ARR; subst; ins.
      by specialize (RESP my_cpumap); des.
  }

  specialize (RESP my_cpumap); des; specialize (RESP0 sched MULT ARRts j).
  exploit RESP0.
    by unfold job_of, beq_task; destruct (task_eq_dec); ins.
    by instantiate (1 := 0); unfold my_arr_seq, arrives_at in *; rewrite mem_seq1; apply/eqP.
    unfold completed, service; simpl; move => /eqP SUM; rewrite -SUM add0n.
    apply leq_trans with (n := \sum_(0 <= t < R_tsk) 1);
      last by rewrite sum_nat_const_nat muln1 subn0.
    unfold my_service_at; apply leq_sum; ins; assert (EQ: j == j = true); first by apply/eqP.
    rewrite EQ; destruct (i < task_cost tsk); ins.
Qed.
