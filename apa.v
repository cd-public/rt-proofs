Require Import List Classical ListSet Arith Vbase task job schedule platform priority helper identmp.

(* Set of all possible affinities (mappings from jobs to processors) *)
Definition affinity := job -> set nat.

Definition affinity_non_empty := forall (alpha: affinity) j, ~alpha j = empty_set nat.

(* Whether a schedule is produced by an APA identical multiprocessor *)
Definition apa_ident_mp (num_cpus: nat) (hp: higher_priority) (cpumap: processor_list)
                        (alpha: affinity) (sched: schedule) :=
  (* An identical multiprocessor has a fixed number of cpus *)
  << apa_cpus_nonzero: num_cpus > 0 >> /\
  << apa_num_cpus: forall t, length (cpumap sched t) = num_cpus >> /\

  (* Job is scheduled iff it is mapped to a processor*)
  << apa_mapping: forall j t, List.In (Some j) (cpumap sched t) <-> scheduled sched j t >> /\

  (* A job receives at most 1 unit of service *)
  << apa_max_service: forall j t, service_at sched j t <= 1 >> /\

  (* If a job is scheduled, then its affinity should allow it. *)
  << apa_alpha: forall t j cpu,
          (nth cpu (cpumap sched t) (None) = Some j) -> List.In cpu (alpha j) >> /\

  (* (Weak) APA scheduling invariant *)
  << apa_invariant:
    forall jlow t,
      backlogged sched jlow t <->
        (forall cpu, cpu < num_cpus ->
          List.In cpu (alpha jlow) ->
          (exists (jhigh: job), hp sched t jhigh jlow
                                /\ (nth cpu (cpumap sched t) (None) = Some jhigh))) >>.

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
   ins. exists (fun j => (seq 0 num_cpus)).
   unfold apa_ident_mp; ins; des.
   induction t.
Admitted.


(* Definitions for APA affinity restoration *)

(* Per-task affinities *)
Definition task_affinity (alpha: affinity) :=
   forall (tsk: sporadic_task) (j1 j2: job),
       job_of j1 = Some tsk /\ job_of j2 = Some tsk -> alpha j1 = alpha j2.

Definition inter : set nat -> set nat -> set nat := set_inter eq_nat_dec.

Definition restrict (tsk_i: sporadic_task) (ts: taskset) (alpha: affinity) (alpha': affinity) :=
  << ALPHA: task_affinity alpha >> /\
  << ALPHA': task_affinity alpha' >> /\
  forall tsk j j_i (INtsk: In tsk ts) (INtsk_i: In tsk_i ts) (JOBj: job_of j = Some tsk)
         (JOBj_i: job_of j_i = Some tsk_i), alpha' j = inter (alpha j) (alpha j_i).

(* Service invariant from APA paper *)
Lemma APA_service_invariant :
  forall num_cpus sched hp cpumap ts alpha alpha' tsk_i j t
         (APA: apa_ident_mp num_cpus hp cpumap alpha sched) (INtsk_i: In tsk_i ts)
         (ALPHAtsk: task_affinity alpha) (ALPHA'tsk: task_affinity alpha')
         (RESTR: restrict tsk_i ts alpha alpha'),
    exists sched' cpumap',
       << APA': apa_ident_mp num_cpus hp cpumap' alpha' sched' >> /\
       << SERV: service sched j t >= service sched' j t >>.
Proof.
    intros.
    Admitted.