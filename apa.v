Add LoadPath "/home/felipec/dev/coq/rt-scheduling-spec".
Require Import Coq.Lists.List.
Require Export ListSet.
Require Export Arith.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import task.
Require Import job.
Require Import schedule.
Require Import priority.
Require Import helper.
Require Import identmp.

(* Set of all possible affinities (mappings from jobs to processors) *)
Definition affinity := job -> set nat.

Definition affinity_non_empty := forall (alpha: affinity) (j: job), ~alpha j = empty_set nat.

(* Whether a schedule is produced by an APA identical multiprocessor *)
Record apa_ident_mp (num_cpus: nat) (sched: schedule) (hp: higher_priority)
                    (cpumap: processor_list) (alpha: affinity) : Prop :=
  {
    (* An identical multiprocessor has a fixed number of cpus *)
    apa_ident_mp_cpus_nonzero: num_cpus > 0;
    apa_ident_mp_num_cpus: forall (t: time), length (cpumap sched t) = num_cpus;

    (* Job is scheduled iff it is mapped to a processor*)
    apa_ident_mp_mapping: forall (j: job) (t: time),
                              List.In (Some j) (cpumap sched t)
                                  <-> scheduled sched j t;

    (* A job receives at most 1 unit of service *)
    apa_ident_mp_sched_unit: forall (j: job) (t: time), service_at sched j t <= 1;

    (* If a job is scheduled, then its affinity should allow it. *)
    apa_ident_mp_restricted_affinities:
        forall (t: time) (j: job) (cpu: nat),
            (nth cpu (cpumap sched t) (None) = Some j) -> List.In cpu (alpha j);

    (* (Weak) APA scheduling invariant *)
    apa_ident_mp_invariant:
        forall (jlow: job) (t: time),
            backlogged sched jlow t <->
                (forall (cpu: nat),
                cpu < num_cpus ->
                List.In cpu (alpha jlow) ->
                    (exists (jhigh: job),
                        hp jhigh jlow sched t
                        /\ (nth cpu (cpumap sched t) (None) = Some jhigh)))
  }.

(* Proof that an APA multiprocessor with global affinities is the same as
   an identical multiprocessor with equal number of cpus *)
Lemma exists_apa_platform_that_is_global :
    forall (num_cpus: nat) (sched: schedule) (hp: higher_priority) (cpumap: processor_list),
        ident_mp num_cpus sched hp cpumap ->
        schedule_independent hp ->
        exists (alpha: affinity),
            forall (sched': schedule) (cpumap': processor_list),
                apa_ident_mp num_cpus sched' hp cpumap' alpha ->
                arr_seq sched = arr_seq sched' ->
                    (forall (j: job) (t: time), service sched j t = service sched' j t).
Proof. intros num_cpus sched hp cpumap sched_is_identmp sched_ind.
       inversion_clear sched_is_identmp as [num_cpus_positive _ _ _ invariant_sched].
       exists (fun (j : job) => (seq 0 num_cpus)).
       intros sched' cpumap' sched'_is_apa same_arr j t.
       inversion_clear sched'_is_apa as [num_cpus_sched' _ _ _ _ invariant_sched'].
       specialize (invariant_sched j t).
       specialize (invariant_sched' j t).

       induction t.
       intros.
       simpl.
       destruct (excluded_middle (backlogged sched j 0)) as [j_backlogged_sched | j_not_backlogged_sched].
       destruct (excluded_middle (backlogged sched' j 0)) as [j_backlogged_sched' | j_not_backlogged_sched'].

       - rewrite 2 backlogged_no_service; trivial.
       - rewrite 2 backlogged_no_service; trivial.
         apply invariant_sched'. intros cpu cpu_less in_cpu.
         inversion_clear invariant_sched as [invariant_sched_suf _].
         specialize (invariant_sched_suf j_backlogged_sched).

         assert (bla : forall cpu0 : nat, 
                      cpu0 < num_cpus ->
                      exists jhigh : job,
                        hp jhigh j sched' 0 /\
                        exists cpu', cpu' < num_cpus /\ nth cpu' (cpumap sched' 0) None = Some jhigh).
         admit.
         apply (bla cpu cpu_less).

         assert (bla := invariant_sched_j_suf cpu cpu_less).
         inversion bla as [jhigh [H1 H2]].
         assert (H00 : ~backlogged sched' jhigh 0).
         rewrite invariant_sched'.
         unfold not. intros.

         inversion_clear invariant_sched' as [_ invariant_sched'_nec].
         apply invariant_sched'_nec.

         intros.
         specialize (invariant_sched_suf cpu H).




         induction cpu.
             intros.
             specialize (invariant_sched_suf 0 H).
             inversion invariant_sched_suf as [jhigh [H1 H2]].
             destruct (excluded_middle (backlogged sched' jhigh 0)).
         apply contrapositive in invariant_sched'_nec; trivial.
         apply invariant_sched'_nec.
         intros cpu cpu_less in_cpu.
         

inversion invariant_sched' as [_ invariant_sched'_nec].
         
         
         apply contrapositive in invariant_sched'_nec; trivial.
         
         apply not_all_ex_not in invariant_sched'_nec.
         inversion invariant_sched'_nec as [cpu invariant_neg].
         apply imply_to_and in invariant_neg.
         inversion invariant_neg as [cpu_less invariant_neg2].
         apply imply_to_and in invariant_neg2.
         inversion invariant_neg2 as [in_cpu no_jobs_hp].
         assert (H : ~ (forall cpu : nat,
                    cpu < num_cpus ->
                    In cpu (seq 0 num_cpus) ->
                    exists jhigh : job,
                      hp jhigh j sched' 0 /\
                      nth cpu (cpumap' sched' 0) None = Some jhigh)).
         unfold not. intros.
         specialize (H cpu cpu_less in_cpu).
         apply no_jobs_hp. apply H.


(* Definitions for APA affinity restoration *)

(* Per-task affinities *)
Definition task_affinity (alpha: affinity) :=
   forall (tsk: sporadic_task) (j1 j2: job),
       job_of j1 = Some tsk /\ job_of j2 = Some tsk -> alpha j1 = alpha j2.

Definition inter : set nat -> set nat -> set nat := set_inter eq_nat_dec.

Definition restrict (tsk_i: sporadic_task) (ts: taskset)
                    (alpha: affinity) (alpha': affinity) : Prop :=
    task_affinity alpha
    /\ task_affinity alpha'
    /\ (forall (tsk: sporadic_task) (j: job) (j_i: job),
         In tsk ts /\ In tsk_i ts
         /\ job_of j = Some tsk /\ job_of j_i = Some tsk_i
         -> alpha' j = inter (alpha j) (alpha j_i)).

(* Service invariant from APA paper *)
Lemma APA_service_invariant :
    forall (num_cpus: nat) (sched: schedule) (hp: higher_priority) (cpumap: processor_list)
           (ts: taskset) (alpha: affinity) (alpha': affinity) (tsk_i: sporadic_task)
           (j: job) (t: time),
               apa_ident_mp num_cpus sched hp cpumap alpha
               /\ In tsk_i ts
               /\ task_affinity alpha /\ task_affinity alpha'
               /\ restrict tsk_i ts alpha alpha'
               -> exists (sched': schedule) (cpumap': processor_list),
                      (apa_ident_mp num_cpus sched' hp cpumap' alpha'
                       /\ service sched j t >= service sched' j t).
Proof.
    intros.
    Admitted.