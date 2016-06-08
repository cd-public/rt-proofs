Require Import rt.util.all.
Require Import rt.model.apa.task rt.model.apa.job rt.model.apa.schedule
               rt.model.apa.priority rt.model.apa.task_arrival
               rt.model.apa.interference rt.model.apa.affinity.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.

Module Platform.

  Import Job SporadicTaskset ScheduleOfSporadicTask SporadicTaskset
         SporadicTaskArrival Interference Priority Affinity.

  Section Properties.
    
    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.
    Variable task_deadline: sporadic_task -> time.
    
    Context {Job: eqType}.
    Variable job_cost: Job -> time.
    Variable job_deadline: Job -> time.
    Variable job_task: Job -> sporadic_task.
    
    (* Assume any job arrival sequence ... *)
    Context {arr_seq: arrival_sequence Job}.

    (* ... and any schedule of this arrival sequence. *)
    Context {num_cpus: nat}.
    Variable sched: schedule num_cpus arr_seq.

    (* Assume that every task has a processor affinity alpha. *)
    Variable alpha: task_affinity sporadic_task num_cpus.
    
    Section Execution.

      (* A schedule is work-conserving iff when a job j is backlogged, all
         processors *on which j can be scheduled* are busy with other jobs. *)
      Definition apa_work_conserving :=
        forall j t,
          backlogged job_cost sched j t ->
          forall cpu,
            can_execute_on alpha (job_task j) cpu ->
            exists j_other,
              scheduled_on sched j_other cpu t.

      (* In a schedule that enforces affinities, a job is scheduled
         only if its affinity allows it. *)
      Definition respects_affinity :=
        forall j cpu t,
          scheduled_on sched j cpu t ->
          can_execute_on alpha (job_task j) cpu.

    End Execution.

    Section JLDP.

      (* A JLFP/JLDP policy ...*)
      Variable higher_eq_priority: JLDP_policy arr_seq.

      (* ... is enforced by a weak APA scheduler iff at any time t,
         for any backlogged job j, if there is another job j_hp
         executing on j's affinity, then j_hp's priority must be
         as high as j's priority. *)
      Definition enforces_JLDP_policy_under_weak_APA :=
        forall (j j_hp: JobIn arr_seq) cpu t,
          backlogged job_cost sched j t ->
          scheduled_on sched j_hp cpu t ->
          can_execute_on alpha (job_task j) cpu ->
          higher_eq_priority t j_hp j.
      
    End JLDP.
    
    Section FP.

      (* Given an FP policy, ...*)
      Variable higher_eq_priority: FP_policy sporadic_task.

      (* ... this policy is enforced by a weak APA scheduler iff
         the corresponding JLDP policy is enforced by the scheduler. *)
      Definition enforces_FP_policy_under_weak_APA :=
        enforces_JLDP_policy_under_weak_APA (FP_to_JLDP job_task higher_eq_priority).

    End FP.

  End Properties.
  
End Platform.