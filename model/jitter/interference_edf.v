Add LoadPath "../.." as rt.
Require Import rt.util.Vbase rt.util.lemmas.
Require Import rt.model.jitter.task rt.model.jitter.job rt.model.jitter.schedule
               rt.model.jitter.priority rt.model.jitter.task_arrival rt.model.jitter.interference
               rt.model.jitter.arrival_sequence rt.model.jitter.platform.
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.

Module InterferenceEDF.

  Import ScheduleWithJitter Priority Platform Interference Priority.
  
  Section Lemmas. 

    Context {Job: eqType}.
    Variable job_cost: Job -> nat.
    Variable job_deadline: Job -> nat.
    Variable job_jitter: Job -> nat.
    
    (* Assume any job arrival sequence... *)
    Context {arr_seq: arrival_sequence Job}.

    (* Consider any schedule. *)
    Variable num_cpus: nat.
    Variable sched: schedule num_cpus arr_seq.
    
    (* Assume that the schedule satisfies the global scheduling invariant
       for EDF, i.e., if any job of tsk is backlogged, every processor
       must be busy with jobs with no larger absolute deadline. *)
    Hypothesis H_scheduler_uses_EDF:
      enforces_JLDP_policy job_cost job_jitter sched (EDF job_deadline). 

    (* Under EDF scheduling, a job only causes interference if its deadline
       is not larger than the deadline of the analyzed job. *)
    Lemma interference_under_edf_implies_shorter_deadlines :
      forall (j j': JobIn arr_seq) t1 t2,
        job_interference job_cost job_jitter sched j' j t1 t2 != 0 ->
        job_arrival j + job_deadline j <= job_arrival j' + job_deadline j'.
    Proof.
      rename H_scheduler_uses_EDF into PRIO.
      intros j j' t1 t2 INTERF.
      unfold job_interference in INTERF.
      destruct ([exists t': 'I_t2, (t' >= t1) && backlogged job_cost job_jitter sched j' t' &&
                                              scheduled sched j t']) eqn:EX.
      {
        move: EX => /existsP EX; destruct EX as [t' EX];move: EX => /andP [/andP [LE BACK] SCHED].
        by eapply PRIO in SCHED; last by apply BACK.
      }
      {
        apply negbT in EX; rewrite negb_exists in EX; move: EX => /forallP ALL. 
        rewrite big_nat_cond (eq_bigr (fun x => 0)) in INTERF;
          first by rewrite -big_nat_cond big_const_nat iter_addn mul0n  addn0 eq_refl in INTERF.
        intros i; rewrite andbT; move => /andP [GT LT].
        specialize (ALL (Ordinal LT)); simpl in ALL.
        rewrite -andbA negb_and -implybE in ALL; move: ALL => /implyP ALL.
        by specialize (ALL GT); apply/eqP; rewrite eqb0.
      }
    Qed.

  End Lemmas.

End InterferenceEDF.