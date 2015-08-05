Require Import Vbase job task schedule task_arrival response_time platform
        schedulability divround helper priority identmp helper workload
        ssreflect ssrbool eqtype ssrnat seq div fintype bigop path ssromega.

Definition interference_bound := sporadic_task -> sporadic_task -> time -> time -> time.

Definition I_fp (hp: task_hp_relation) : interference_bound :=
  fun (tsk other: sporadic_task) (R_other delta: time) =>
    if hp other tsk then W other R_other delta else 0.

Definition I_jlfp (hp: sched_job_hp_relation) : interference_bound :=
  fun (tsk other: sporadic_task) (R_other delta: time) =>
    if other != tsk then W other R_other delta else 0.

Definition rt_analysis_eq (ts: taskset) (tsk: sporadic_task) (I: interference_bound)
                          (R_other: sporadic_task -> time) (num_cpus R_tsk: time) :=
  R_tsk == task_cost tsk + (\sum_(i <- ts) I tsk i (R_other i) R_tsk) %/ num_cpus.

Section RTA_FP.

Definition rt_analysis_fp (hp: task_hp_relation) (ts: taskset) (tsk: sporadic_task)
                          (R_other: sporadic_task -> time) (num_cpus R_tsk: time) :=
  (rt_analysis_eq ts tsk (I_fp hp) R_other num_cpus R_tsk) && (R_tsk <= task_deadline tsk).

Definition schedulable_hp (plat: processor_platform) (ts: taskset) (tsk_hp: task_hp_relation) 
                           (tsk: sporadic_task) :=
  forall tsk' (IN: tsk' \in ts) (HPother: tsk_hp tsk' tsk),
    schedulable_task plat ts tsk'.

Definition rt_bound_hp (plat: processor_platform) (ts: taskset) (tsk_hp: task_hp_relation) 
                       (R_other: sporadic_task -> time) (tsk: sporadic_task) :=
  forall tsk' (IN: tsk' \in ts) (HPother: tsk_hp tsk' tsk),
    response_time_ub plat ts tsk' (R_other tsk').

Theorem rt_bound_fp :
  forall ts sched (SPO: sporadic_task_model ts sched)
         tsk_hp (VALIDfp: valid_fp_policy tsk_hp)
         hp (VALIDhp: valid_jldp_policy hp) (CONV: convert_fp_jldp tsk_hp hp) 
         cpumap num_cpus (MULT: ident_mp num_cpus hp cpumap sched)
         (RESTR: restricted_deadline_model ts) tsk (IN: tsk \in ts)
         (SCHEDhp: schedulable_hp (ident_mp num_cpus hp cpumap) ts tsk_hp tsk)
         R_hp (RThp: forall cpumap, rt_bound_hp (ident_mp num_cpus hp cpumap) ts tsk_hp R_hp tsk)
         R_tsk (ANALYSIS: rt_analysis_fp tsk_hp ts tsk R_hp num_cpus R_tsk),
    (forall cpumap, response_time_ub (ident_mp num_cpus hp cpumap) ts tsk R_tsk).
Proof.
Admitted.

End RTA_FP.

Section RTA_JLFP.
  
Definition rt_analysis_jlfp (hp: sched_job_hp_relation) (ts: taskset) (tsk: sporadic_task)
                            (R_other: sporadic_task -> time) (num_cpus R_tsk: time) :=
  (rt_analysis_eq ts tsk (I_jlfp hp) R_other num_cpus R_tsk) && (R_tsk <= task_deadline tsk).

End RTA_JLFP.