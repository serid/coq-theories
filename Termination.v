Print Acc.
Print Fix.

Lemma acc_ltO : Acc lt O.
constructor; intros.
inversion H.
Qed.

Lemma acc_ltN n : Acc lt n -> Acc lt (S n).
intro H0.
constructor; intros.
unfold lt in H.
inversion H.
- assumption.
- clear m H1.
apply H0.
assumption.
Qed.

Lemma wf_lt : well_founded lt.
intro n.
induction n.
- exact acc_ltO.
- apply acc_ltN. assumption.
Qed.

Require Extraction.

Recursive Extraction Fix.