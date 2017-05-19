Require Import rt.util.all.
Require Import rt.model.time rt.model.arrival.basic.job rt.model.arrival.basic.task rt.model.arrival.basic.arrival_sequence rt.model.priority.
Require Import rt.model.schedule.uni.schedule rt.model.schedule.uni.schedulability rt.model.schedule.uni.basic.platform.
Require Import rt.analysis.uni.basic.edf.total_service rt.analysis.uni.basic.edf.demand.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.

Module EDFDemandAnalysis.

  Import UniprocessorSchedule Schedulability Priority Platform Job Demand.

  (* In this section, we prove some useful lemmas about demand and
     schedules which respect EDF. *)

  Section Lemmas.

    Context {Task: eqType}.
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_deadline: Job -> time.
    Variable job_task: Job -> Task.

    (* Consider any job arrival sequence with no duplicate jobs... *)
    Context {arr_seq: arrival_sequence Job}.
    Hypothesis H_arrival_sequence_is_a_set:
      arrival_sequence_is_a_set arr_seq.

    (* ... and any schedule of this arrival sequence. *)
    Variable sched: schedule Job.

    (* Assume that all jobs have valid job parameter and... *)
    Hypothesis H_valid_job_parameters:
      forall (j: Job),
        valid_realtime_job job_cost job_deadline j.
    (* ...and that jobs only execute after they arrived ... *)
    Hypothesis H_jobs_must_arrive_to_execute:
      jobs_must_arrive_to_execute job_arrival sched.
    (* ...and don't execute after they completed. *)
    Hypothesis H_completed_jobs_dont_execute:
      completed_jobs_dont_execute job_cost sched.


    (* For simplicity, let us define some local names about demand. *)
    Let absolute_deadline (j: Job) := job_arrival j + job_deadline j.
    Let demand_at := total_demand_at job_arrival job_cost job_deadline arr_seq.
    Let deadline_le := jobs_with_deadline_le job_arrival job_deadline arr_seq.
    
    (* In this section, we prove that the demand gives a sufficient
       condition for schedulability under EDF. *)
    Section DemandUnderEDF.

      (* Let sched be any EDF schedule ... *)
      Hypothesis H_edf_policy:
        respects_JLFP_policy job_arrival job_deadline arr_seq sched (EDF job_arrival job_deadline).

      (* ... with a deadline miss at time t_f by job j_mis ... *)
      
      Definition deadline_miss (j:Job) := service sched j (absolute_deadline j) < job_cost j.
      Definition deadline_miss_at (j:Job) (t:time) := (t = absolute_deadline j) /\ deadline_miss j.
      
      Variable t_f : time.
      Variable j_mis : Job.
      
      Hypothesis H_deadline_miss:  deadline_miss_at j_mis t_f.

      (* ... WLOG, j_mis is the only job with deadline at t_f ... *)

      Hypothesis H_j_mis_only: forall j, (absolute_deadline j) = t_f -> j = j_mis.

      (* ... and no prior misses ... *)

      Hypothesis H_no_prior_miss:
        forall (j:Job), (absolute_deadline j) < t_f ->
                        service sched j (absolute_deadline j) == job_cost j.

      (* ... with busy interval taken WLOG to be the entire analyzed interval ... *)
      
      Definition fully_scheduled t := forall t1, t1 <= t -> ~~is_idle sched t1.
      Definition work_relevant t := forall j, (absolute_deadline j) <= t.
      Definition busy_interval t := fully_scheduled t /\ work_relevant t.
      
      Hypothesis H_busy_interval: busy_interval t_f.

      (* ... in which we only concern ourselves with jobs with arrival in the interval *)

      Hypothesis H_arrival_in_interval: forall j, j \in jobs_arrived_up_to arr_seq t_f.

      (* ... demand must have exceeded the interval length. *)
      Theorem deadline_miss_in_edf_implies_demand_gt_interval:
        demand_at t_f > t_f.
      Proof.
        unfold respects_JLFP_policy, arrives_in, backlogged, scheduled_at, EDF, pending, has_arrived, completed_by, service, service_during, service_at, scheduled_at, jobs_arriving_at in H_edf_policy.
        unfold demand_at, total_demand_at, jobs_with_deadline_le.
        unfold deadline_miss_at, deadline_miss in H_deadline_miss.
        unfold busy_interval, fully_scheduled, work_relevant, is_idle in H_busy_interval.
        
        Admitted.
      
    End DemandUnderEDF.

  End Lemmas.

End EDFDemandAnalysis.