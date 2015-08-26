Require Import Vbase TaskDefs JobDefs TaskArrivalDefs ScheduleDefs PlatformDefs helper
                ssreflect ssrbool eqtype ssrnat seq fintype bigop.

Module ResponseTime.

  Import Schedule SporadicTaskset SporadicTaskArrival.

  Section ResponseTimeBound.

    Context {Job: eqType}.
    Variable job_arrival: Job -> nat.
    Variable job_cost: Job -> nat.
    Variable job_task: Job -> sporadic_task.
  
    Variable num_cpus: nat.
    Variable rate: Job -> processor -> nat.
    Variable schedule_of_platform: schedule Job -> Prop.
  
    Variable tsk: sporadic_task.

    Definition job_has_completed_by (sched: schedule Job) :=
      completed job_cost num_cpus rate sched.
    
    Definition response_time_ub_task (response_time_bound: time) :=
      forall (sched: schedule Job) (j: Job),
        job_task j == tsk ->
        schedule_of_platform sched ->
        job_has_completed_by sched j (job_arrival j + response_time_bound).

    Section BasicLemmas.
  
      Variable sched: schedule Job.
      Hypothesis platform: schedule_of_platform sched.

      Variable response_time_bound: time.
      Hypothesis is_response_time_bound:
        response_time_ub_task response_time_bound.

      Variable j: Job.
      Hypothesis job_of_task: job_task j == tsk.

      Hypothesis comp_jobs_dont_exec:
        completed_job_doesnt_exec job_cost num_cpus rate sched.

      Lemma service_at_after_rt_zero :
        forall t' (GE: t' >= job_arrival j + response_time_bound),
          service_at num_cpus rate sched j t' = 0.
      Proof.
        rename response_time_bound into R, is_response_time_bound into RT,
               comp_jobs_dont_exec into EXEC; ins.
        unfold response_time_ub_task, job_has_completed_by, completed,
               completed_job_doesnt_exec in *.
        specialize (RT sched j job_of_task platform).
        apply/eqP; rewrite -leqn0.
        rewrite <- leq_add2l with (p := job_cost j).
        move: RT => /eqP RT; rewrite -{1}RT addn0.
        apply leq_trans with (n := service num_cpus rate sched j t'.+1); last by apply EXEC.
        unfold service; rewrite -> big_cat_nat with (p := t'.+1) (n := job_arrival j + R);
          [rewrite leq_add2l /= | by ins | by apply ltnW].
        by rewrite big_nat_recr // /=; apply leq_addl.
      Qed.

      Lemma sum_service_after_rt_zero :
        forall t' (GE: t' >= job_arrival j + response_time_bound) t'',
          \sum_(t' <= t < t'') service_at num_cpus rate sched j t = 0.
      Proof.
        ins; apply/eqP; rewrite -leqn0.
        rewrite big_nat_cond; rewrite -> eq_bigr with (F2 := fun i => 0);
          first by rewrite big_const_seq iter_addn mul0n addn0 leqnn.
        intro i; rewrite andbT; move => /andP [LE _].
        by rewrite service_at_after_rt_zero; [by ins | by apply leq_trans with (n := t')].
      Qed.

    End BasicLemmas.

  End ResponseTimeBound.
  
End ResponseTime.
  





  
  
(*Variable plat: processor_platform.
Variable ts: sporadic_taskset.
Variable tsk: sporadic_task.

Definition response_time_ub (R: time) :=
  forall (sched: schedule) (PLAT: plat sched)
         j (JOBof: job_task j == tsk)
         t_a (ARRj: arrives_at sched j t_a),
    completed sched j (t_a + R).


Import SporadicTaskJob SporadicTaskset Platform.

Definition my_service_at (my_j j: job) (t: time) :=
  if my_j == j then
    (if t < task_cost (job_task j) then 1 else 0)
  else 0.

Definition my_arr_seq (my_j: job) (t: nat) :=
  if (t == 0) then [::my_j] else [::].

Section ResponseTimeGEQCost.

Variable ts: sporadic_taskset.
Variable tsk: sporadic_task.  
Hypothesis in_ts: tsk \in ts.

Variable R_tsk: time.
Variable platform: processor_platform.
Hypothesis rt_bound: response_time_ub platform tsk R_tsk.
(*Hypothesis exists_sched:
  forall arr_seq, exists (sched: schedule), arr_list sched = arr_seq /\ platform sched.*)

Hypothesis service_lt_one :
  forall (sched: schedule) (PLAT: platform sched), max_service_one sched.

Lemma rt_geq_wcet_identmp : R_tsk >= task_cost tsk.  
Proof.
  rename rt_bound into RESP.
  unfold response_time_ub in *; ins; des.
  
  (*have PROP := task_properties tsk; des.*)

 (* assert (VALIDj:  << X1: 0 < task_cost tsk >> /\
                   << X2: task_cost tsk <= task_deadline tsk >> /\
                   << X3: 0 < task_deadline tsk >> /\
                   << X4: task_cost tsk <= task_cost tsk >> /\
                   << X5: task_deadline tsk = task_deadline tsk >> ).
    by repeat split; ins; try apply leqnn; clear tmp_job; rename x0 into j.*)    
  set j := Build_job 0 (task_cost tsk) (task_deadline tsk) tsk VALIDj.

  assert (VALIDarr: << NOMULT: forall (j0 : job_eqType) (t1 t2 : time),
                         j0 \in my_arr_seq j t1 -> j0 \in my_arr_seq j t2 -> t1 = t2 >> /\
                    << ARR_PARAMS: forall (j0 : job_eqType) (t : time),
                         j0 \in my_arr_seq j t -> job_arrival j0 = t >> /\
                    << UNIQ: forall t, uniq (my_arr_seq j t)>>).
  {
    repeat split; try red.
      by intros j0 t1 t2 ARR1 ARR2; unfold my_arr_seq in *; destruct t1, t2; ins.
      intros j0 t ARRj0; unfold my_arr_seq in *; destruct t; simpl in *.
        by move: ARRj0; rewrite mem_seq1; move => /eqP ARRj0; subst.
        by rewrite in_nil in ARRj0.
      by intros t; unfold my_arr_seq; destruct (t == 0).
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
      have jPROP := job_properties j; des; simpl in *.
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

  specialize (EX arr); des.

  assert (ARRts: ts_arrival_sequence ts sched).
  {
    unfold ts_arrival_sequence; ins.
    unfold arrives_at in ARR; rewrite EX /= in ARR.
    unfold my_arr_seq in ARR; simpl in ARR.
    destruct (t == 0); last by rewrite in_nil in ARR.
    by move: ARR; rewrite mem_seq1; move => /eqP ARR; subst; ins.
  }

  unfold response_time_ub in RESP; des; specialize (RESP0 sched EX0 ARRts j).
  exploit RESP0.
    by apply/eqP.
    by instantiate (1 := 0); unfold arrives_at; rewrite EX /=; unfold my_arr_seq, arrives_at in *;
      rewrite mem_seq1; apply/eqP.
    unfold completed, service; simpl; move => /eqP SUM; rewrite -SUM add0n.
    apply leq_trans with (n := \sum_(0 <= t < R_tsk) 1);
      last by rewrite sum_nat_const_nat muln1 subn0.
    by apply leq_sum; intros t _; apply service_lt_one, EX0.
Qed.*)