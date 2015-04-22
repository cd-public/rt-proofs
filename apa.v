Add LoadPath "/home/felipec/dev/coq/rt-scheduling-spec".
Require Import Coq.Lists.List.
Require Export ListSet.
Require Export Arith.
Require Import Coq.Arith.Peano_dec.
Require Import job.
Require Import schedule.
Require Import priority.
Require Import helper.
Require Import identmp.

(* Set of all possible affinities (mappings from jobs to processors) *)
Definition affinity := job -> set nat.

Axiom affinity_non_empty : forall (alpha: affinity) (j: job), ~alpha j = empty_set nat.

(* Whether a schedule is produced by an APA identical multiprocessor *)
Record apa_ident_mp (num_cpus: nat) (sched: schedule)
                    (alpha: affinity) (hp: higher_priority) : Prop :=
  {
    (* An identical multiprocessor has a fixed number of cpus *)
    apa_ident_mp_cpus_nonzero: num_cpus > 0;
    apa_ident_mp_num_cpus: forall (t: time), length (cpumap sched t) = num_cpus;

    (* Job is scheduled iff it is mapped to a processor*)
    apa_ident_mp_mapping: forall (j: job) (t: time),
                              List.In (Some j) (cpumap sched t) <-> sched j t = 1;

    (* A scheduled job only receives 1 unit of service *)
    apa_ident_mp_sched_unit: forall (j: job) (t: time), sched j t <= 1;

    (* If a job is scheduled, then its affinity should allow it. *)
    apa_ident_mp_restricted_affinities:
        forall (t: time) (j: job) (cpu: nat),
            (nth cpu (cpumap sched t) (None) = Some j) -> List.In cpu (alpha j);

    (* (Weak) APA scheduling invariant *)
    apa_ident_mp_invariant:
        forall (jlow: job) (t: time),
            backlogged sched jlow t <->
                (forall (cpu: nat),
                cpu < num_cpus /\
                List.In cpu (alpha jlow) ->
                    (exists (jhigh: job),
                        hp jhigh jlow sched t
                        /\ (nth cpu (cpumap sched t) (None) = Some jhigh)))
  }.

(* Proof that an APA multiprocessor with global affinities is the same as
   an identical multiprocessor with equal number of cpus *)
Lemma exists_apa_platform_that_is_global :
    forall (num_cpus: nat) (sched: schedule) (hp: higher_priority),
        ident_mp num_cpus sched hp ->
        exists (sched': schedule) (alpha: affinity),
            apa_ident_mp num_cpus sched alpha hp
            /\ (forall (j: job) (t: time), service sched j t = service sched' j t).
Proof. intros. inversion H. exists sched. exists (fun (j : job) => (seq 0 num_cpus)).
       split. split.
       apply ident_mp_cpus_nonzero.
       apply ident_mp_num_cpus.
       apply ident_mp_mapping.
       apply ident_mp_sched_unit.
       intros. apply nat_seq_nth_In.
       rewrite <- (ident_mp_num_cpus t). apply element_in_list_no_overflow with (x := j).
       apply H0.
       intros. assert (H1 := ident_mp_invariant jlow t).
       inversion H1. split.
       intros. assert (H5 := H0 H3 cpu). inversion H4.
       apply H5 in H6. trivial.
       intros. apply H2. intros.
       assert (H5 := H3 cpu). assert (H6 := nat_seq_nth_In num_cpus cpu H4).
       assert (H7 := H5 (conj H4 H6)). trivial. trivial.
Qed.

(* Definitions for APA affinity restoration *)

(* Per-task affinities *)
Definition task_affinity (alpha: affinity) :=
   forall (tsk: sporadic_task) (j1 j2: job),
       job_of j1 tsk /\ job_of j2 tsk -> alpha j1 = alpha j2.

Definition inter : set nat -> set nat -> set nat := set_inter eq_nat_dec.

Definition restrict (tsk_i: sporadic_task) (ts: taskset)
                    (alpha: affinity) (alpha': affinity) : Prop :=
    task_affinity alpha
    /\ task_affinity alpha'
    /\ (forall (tsk: sporadic_task) (j: job) (j_i: job),
         In tsk ts /\ In tsk_i ts
         /\ job_of j tsk /\ job_of j_i tsk_i
         -> alpha' j = inter (alpha j) (alpha j_i)).

(* Service invariant from APA paper *)
Lemma APA_service_invariant :
    forall (num_cpus: nat) (sched: schedule) (hp: higher_priority)
           (ts: taskset) (alpha: affinity) (alpha': affinity) (tsk_i: sporadic_task)
           (j: job) (t: time),
               apa_ident_mp num_cpus sched alpha hp
               /\ In tsk_i ts
               /\ task_affinity alpha /\ task_affinity alpha'
               /\ restrict tsk_i ts alpha alpha'
               -> exists (sched': schedule),
                      (apa_ident_mp num_cpus sched' alpha' hp
                       /\ service sched j t >= service sched' j t).
Proof.
    intros.
    Admitted.