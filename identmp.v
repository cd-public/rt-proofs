Require Import Vbase List job schedule priority platform.

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

(*Require Export Coq.Structures.OrderedTypeEx.*)

(* Just playing a bit with Finite Maps

Module M := FMapList.Make(Nat_as_OT).
Definition cpumap: Type := M.t job.
Definition find k (m: cpumap) := M.find k m.
Definition update (p: cpu * job) (m: cpumap) :=
  M.add (fst p) (snd p) m.
Notation "k |-> v" := (pair k v) (at level 60).
Notation "[ ]" := (M.empty job).
Notation "[ p1 , .. , pn ]" := (update p1 .. (update pn (M.empty job)) .. ).

Variable job1 job2 job3: job.
Variable mapped: time -> cpumap.

Example ex1: find 3 [1 |-> job1, 3 |-> job2] = Some job2.
Proof. reflexivity. Qed.

Example ex2: find 2 [3 |-> job2] = None.
Proof. reflexivity. Qed.

(* Mapping from processors to tasks at time t *)
Definition job_mapping := time -> cpumap.*)
