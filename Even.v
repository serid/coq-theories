(** Parity predicate and some facts about it **)

Require Bool.

Definition no_fixpoint_negb := Bool.no_fixpoint_negb.
Definition negb_involutive := Bool.negb_involutive.

Definition decidable (P : Prop) := P \/ ~ P.

(** Parity function **)
Fixpoint even (n:nat) : bool := match n with
  | 0 => true
  | S n' => negb (even n')
end.

(** Parity predicate **)
Inductive Even : nat -> Prop :=
  | even_f : forall n:nat, even n = true -> Even n.

Definition Odd (n:nat) := ~ Even n.

Fact even_O : Even O.
apply even_f. reflexivity.
Qed.

(** A dual to even_f **)
Fact even_reverse : forall n:nat, Even n -> even n = true.
intros.
destruct H. exact H.
Qed.

Fact even2 : forall n:nat, Even (S (S n)) <-> Even n.
intros.
split.
- intro. apply even_reverse in H.
unfold even in H. fold even in H. rewrite negb_involutive in H. apply (even_f n H).
- intro. apply even_f.
unfold even. fold even. rewrite negb_involutive. apply (even_reverse n H).
Qed.

Fact odd2 : forall n:nat, Odd (S (S n)) <-> Odd n.
intros.
apply not_iff_compat. apply even2.
Qed.

Fact odd_follows : forall n:nat, Even n -> Odd (S n).
intros.
intro.
apply even_reverse in H. apply even_reverse in H0.
rewrite <- H0 in H. clear H0.
symmetry in H.
apply (no_fixpoint_negb (even n)) in H. exact H.
Qed.

Fact odd_preceedes : forall n:nat, Even (S n) -> Odd n.
intro.
intro.
intro.
apply (odd_follows n H0 H).
Qed.

(* Alternative proof
Fact odd_preceedes : forall n:nat, Even (S n) -> Odd n.
intros.
intro.
apply even_reverse in H. apply even_reverse in H0.
rewrite <- H0 in H. clear H0.
symmetry in H.
apply (no_fixpoint_negb (even n)) in H. exact H.
Qed.
*)

Fact odd_reverse : forall n:nat, Odd n -> even n <> true.
intros.
intro.
apply H.
apply even_f. exact H0.
Qed.

Fact even_follows : forall n:nat, Odd n -> Even (S n).
intros.
apply even_f.
apply odd_reverse in H.
destruct n.
- exfalso. apply H. reflexivity.
- unfold even in *.
fold even in *.
destruct (even n). (* this one tactic is as precious as gold *)
* reflexivity.
* exfalso. apply H. reflexivity.
Qed.

Fact even_preceedes : forall n:nat, Odd (S n) -> Even n.
intros.
apply even_f.
apply odd_reverse in H.
destruct n.
- reflexivity.
- unfold even in *.
fold even in *.
destruct (even n). (* this one tactic is as precious as gold *)
* exfalso. apply H. reflexivity.
* reflexivity.
Qed.

Fact even_dec : forall n:nat, {Even n} + {Odd n}.
intros.
induction n.
- left. exact even_O.
- destruct IHn as [a|b].
* right. apply (odd_follows n a).
* left. apply (even_follows n b).
Qed.

Print even_dec.

Fact even_decidable : forall n:nat, decidable (Even n).
intros.
unfold decidable.
destruct (even_dec n) as [a|b].
- left. exact a.
- right. exact b.
Qed.

Fact exlcusive_even_odd : forall n:nat, Even n -> Odd n -> False.
intros. exact (H0 H).
Qed.


(** Some fun facts **)
Fact twelve_is_even : Even 12.
apply (even_f). reflexivity.
Qed.

(** If you pick two numbers three points apart, one of them will be odd **)

Fact any_plus_three : forall n m:nat, (S (S (S n))) = m -> Odd n \/ Odd m.
intros.
assert (equiv : Even n <-> Odd m).
{
  split.
  - intro.
  rewrite <- H.
  apply odd2.
  apply odd_follows.
  exact H0.
  - intro.
  apply even2.
  apply even_preceedes.
  rewrite H.
  exact H0.
}
destruct (even_decidable n).
- right. apply equiv. assumption.
- left. assumption.
Qed.