Require Import Classical Vbase task job schedule platform priority helper identmp.

(* All possible affinity relations *)
Definition affinity := job -> processor_id -> Prop.

Definition affinity_non_empty (alpha: affinity) (num_cpus: nat) (sched: schedule) :=
  forall j arr (ARR: arrives_at sched j arr),
    exists cpu, << MAX: cpu < num_cpus >> /\ << ALPHA: alpha j cpu >>.

(* APA multiprocessor platform *)
Record apa_ident_mp (num_cpus: nat) (hp: sched_job_hp_relation) (sched: schedule) :=
{
  mapped: job_mapping;
  alpha: affinity;

  apa_properties:
    (* The mapping has a finite number of cpus: [1, num_cpus) *)
    << apa_cpus_nonzero: num_cpus > 0 >> /\
    << apa_num_cpus: forall j cpu t, mapped j cpu t -> cpu < num_cpus >> /\

    (* Job is scheduled iff it is mapped to a processor*)
    << apa_mapping: forall j t, scheduled sched j t <-> exists cpu, mapped j cpu t >> /\

    (* Non-parallelism restrictions (mapping must be an injective function) *)
    << mp_mapping_fun: forall j cpu cpu' t, mapped j cpu t /\ mapped j cpu' t -> cpu = cpu' >> /\
    << mp_mapping_inj: forall j j' cpu t, mapped j cpu t /\ mapped j' cpu t -> j = j'>> /\
                                                                  
    (* A job receives at most 1 unit of service *)
    << apa_max_service: forall j t, service_at sched j t <= 1 >> /\

    (* If a job is scheduled, then its affinity should allow it. *)
    << apa_alpha: forall t j cpu, mapped j cpu t -> alpha j cpu >> /\

    (* (Weak) APA scheduling invariant *)
    << apa_invariant: forall jlow t (ARRIVED: arrived sched jlow t),
        backlogged sched jlow t <->
          (exists (j0: job), earlier_job sched j0 jlow /\ pending sched j0 t) \/
          (forall cpu (MAXcpu: cpu < num_cpus) (ALPHA: alpha jlow cpu),
            exists jhigh, hp sched t jhigh jlow /\ mapped jhigh cpu t) >>
}.

(*
(* Proof that an APA multiprocessor with global affinities is the same as
   an identical multiprocessor with equal number of cpus *)
Lemma exists_apa_platform_that_is_global :
  forall num_cpus sched hp cpumap
    (sMult: ident_mp num_cpus hp cpumap sched)
    (hpInd: schedule_independent hp), 
      exists alpha: affinity,
        forall sched' cpumap' j t
          (s'APA: apa_ident_mp num_cpus hp cpumap' alpha sched')
          (arrSame: arrives_at sched = arrives_at sched'),
            service sched j t = service sched' j t.
Proof.
 ins; exists (fun j cpu => True).
 ins; des.
 induction t.
   (* Base case *)
   (* Inductive Step *)
Admitted.

(* Definitions for APA affinity restoration -- IGNORE *)

(* Per-task affinities *)
Definition task_affinity (alpha: affinity) :=
   forall (tsk: sporadic_task) (j1 j2: job),
       job_task j1 = tsk /\ job_task j2 = tsk -> alpha j1 = alpha j2.

Definition restrict (tsk_i: sporadic_task) (ts: taskset) (alpha1 alpha2 alpha': affinity) := True.

(* Service invariant from APA paper *)
Lemma APA_service_invariant :
  forall num_cpus sched hp cpumap ts alpha alpha' (tsk_i: sporadic_task) j t
         (APA: apa_ident_mp num_cpus hp cpumap alpha sched) (INtsk_i: In tsk_i ts)
         (ALPHAtsk: task_affinity alpha) (ALPHA'tsk: task_affinity alpha')
         (*(RESTR: ...)*),
    exists sched' cpumap',
       << APA': apa_ident_mp num_cpus hp cpumap' alpha' sched' >> /\
       << SERV: service sched j t >= service sched' j t >>.
Proof.
    intros.
    Admitted.
*)