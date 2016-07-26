(* The decidable equality for JobIn checks whether the Job
   and the arrival times are the same. *)
Definition jobin_eqdef arr_seq (j1 j2: JobIn arr_seq) :=
  (job_of_job_in j1 == job_of_job_in j2) && (job_arrival j1 == job_arrival j2).
                                                                               
Lemma eqn_jobin : forall arr_seq, Equality.axiom (jobin_eqdef arr_seq).
Proof.
  unfold Equality.axiom; intros arr_seq x y.
  destruct (jobin_eqdef arr_seq x y) eqn:EQ.
  {
    apply ReflectT.
    unfold jobin_eqdef in *.
    move: EQ => /andP [/eqP EQjob /eqP EQarr].
    destruct x, y; ins; subst.
    f_equal; apply bool_irrelevance.
  }
  {
    apply ReflectF.
    unfold jobin_eqdef, not in *; intro BUG.
    apply negbT in EQ; rewrite negb_and in EQ.
    destruct x, y.
    move: EQ => /orP [/negP DIFFjob | /negP DIFFarr].
      by apply DIFFjob; inversion BUG; subst; apply/eqP.
      by apply DIFFarr; inversion BUG; subst; apply/eqP.
  }
Qed.

Canonical jobin_eqMixin arr_seq := EqMixin (eqn_jobin arr_seq).
Canonical jobin_eqType arr_seq := Eval hnf in EqType (JobIn arr_seq) (jobin_eqMixin arr_seq).