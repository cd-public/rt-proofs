Require Import Vbase job schedule priority platform ssrnat.

Definition job_mapping := job -> processor_id -> time -> Prop.

(* Identical multiprocessor platform *)
Definition ident_mp (num_cpus: nat) (hp: sched_job_hp_relation)
                    (mapped: job_mapping) (sched: schedule) :=
  (* The mapping has a finite positive number of cpus: [0, num_cpus) *)
  << mp_cpus_nonzero: num_cpus > 0 >> /\
  << mp_num_cpus: forall j cpu t, mapped t j cpu -> cpu < num_cpus >> /\

  (* Job is scheduled iff it is mapped to some processor*)
  << mp_mapping: forall j t, scheduled sched j t <-> exists cpu, mapped j cpu t >> /\

  (* Non-parallelism restrictions (mapping must be an injective function) *)
  << mp_mapping_fun: forall j cpu cpu' t, mapped j cpu t /\ mapped j cpu' t -> cpu = cpu' >> /\
  << mp_mapping_inj: forall j j' cpu t, mapped j cpu t /\ mapped j' cpu t -> j = j'>> /\
  
  (* A job receives at most 1 unit of service *)
  << mp_max_service: forall j t, service_at sched j t <= 1 >> /\

  (* Global scheduling invariant *)
  << mp_invariant:
    forall jlow t, backlogged sched jlow t <->
      (exists (j0: job), earlier_job sched j0 jlow /\ pending sched j0 t) \/
      (forall cpu (MAXcpu: cpu < num_cpus),
        exists jhigh, hp sched t jhigh jlow /\ mapped jhigh cpu t) >>.