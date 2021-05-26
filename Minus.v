Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.

(*Require Import Compare_dec.
Require Import Coq.Arith.Lt.*)
(*Require Import Lia.*)

(*Print Coq.Init.Peano.*)

Section Numbers.
(* Arithmetic facts *)

(* Tactics:
case -- the weakest one
destruct -- sufficient for most tasks
elim -- recursive destruct
induction -- destruct with induction

inverse

For = and <>:
discriminate.
contradiction.
*)

Fact le_n_0_imp_eq_n_0 (n:nat) : n <= 0 -> n = 0.
intro.
inversion H.
reflexivity.
Qed.

Fact le_0_n (n:nat) : 0 <= n.
elim n.
- apply le_n.
- intros. apply le_S. assumption.
Qed.

Fact le_S_relax_left (n m:nat) : S n <= m -> n <= m.
intro.
elim H; intros.
- apply le_S. apply le_n.
- apply le_S. exact H1.
Qed.

Fact le_S_relax_right (n m:nat) : n <= m -> n <= S m.
apply le_S.
Qed.

Fact le_S_S (n m:nat) : n <= m <-> S n <= S m.
split; intros.
- elim H; intros.
* apply le_n.
* apply le_S. exact H1.
- inversion H.
* apply le_n.
* apply le_S_relax_left. exact H1.
Qed.

Fact nle_0 (n:nat) : ~ S n <= 0.
intro. inversion H.
Qed.

Fact nle_0' (n:nat) : ~ S n <= 0.
exact (fun H =>
    match H with
    end).
Qed.

Fact nle_1_0 : ~ 1 <= 0.
apply nle_0.
Qed.

Definition nle_0_term (n:nat) : ~ S n <= 0 :=
fun e:S n <= 0 =>
let f1 : S n = 0 -> False := fun (e:S n = 0) =>
  eq_ind (S n) (fun e : nat => match e with
                           | 0 => False
                           | S _ => True
                           end) I 0 e
in
let f2 : forall m:nat, S m = 0 -> False := fun (m:nat) (e:S m = 0) =>
  eq_ind (S m) (fun e : nat => match e with
                           | 0 => False
                           | S _ => True
                           end) I 0 e
in
match e in le _ b return (b = 0 -> False) with
  | le_n _ => f1
  | le_S _ m x => f2 m
end eq_refl.

Fact neq_Sn_n (n:nat) : S n <> n.
induction n.
- discriminate.
- injection.
exact IHn.
Qed.

Fact nle_Sn_n (n:nat) : ~ S n <= n.
induction n.
- apply nle_0.
- intro.
apply IHn.
apply le_S_S.
exact H.
Qed.

Print le_ind.

(*Require Import Coq.Program.Equality.*)

Fact le_trans (n m k:nat) : n <= m -> m <= k -> n <= k.
intros.
induction H.
- assumption.
- apply IHle. apply le_S_relax_left in H0. exact H0.
Qed.

Fact le_antisymmetry (n m:nat) : n <= m -> m <= n -> n = m.
intros.
induction H.
- reflexivity.
- apply (le_trans (S m) n m) in H0.
* apply nle_Sn_n in H0. contradiction.
* assumption.
Qed.

Fact le_S4 (n m:nat) : n <= m -> n <> m -> S n <= m.
intros.
induction H.
- contradiction H0. reflexivity.
- apply (proj1 (le_S_S n m)). exact H.
Qed.

Fact lt_irrefl (n:nat) : ~ n < n.
apply nle_Sn_n.
Qed.

Fact lt_assym (n m:nat) : n < m -> ~ m < n.
intro. intro. unfold lt in *.
induction H.
- apply le_S_relax_left in H0. eapply nle_Sn_n. exact H0.
- apply IHle. apply le_S_relax_left. exact H0.
Qed.

Fact nlt_0 (n:nat) : ~ n < 0.
apply nle_0.
Qed.

Fact lt_S_relax_right (n m:nat) : n < m -> n < S m.
apply le_S.
Qed.

Fact exists_Sx (n:nat) : n <> 0 -> (~ forall x:nat, ~ n = S x).
intro.
destruct n.
- contradiction H. reflexivity.
- intro. eapply H0. reflexivity.
Qed.

Fact exists_Sx2 (n:nat) : n <> 0 -> (exists x:nat, n = S x).
intro.
destruct n.
- contradiction H. reflexivity.
- eapply ex_intro. reflexivity.
Qed.

Definition exists_Sx_term (n:nat) : n <> 0 -> (~ forall x:nat, ~ n = S x) :=
fun H : n <> 0 =>
fun H2 : forall x:nat, ~ n = S x =>
match n as n1 return ~ n = n1 with
| O => H
| S n0 => H2 n0
end eq_refl.

Definition exists_Sx2_term (n:nat) : n <> 0 -> (exists x:nat, n = S x) :=
(match n as n0 return (n0 <> 0 -> exists x:nat, n0 = S x) with
| O => fun H : 0 <> 0 =>
  False_ind _ (H eq_refl)
| S x0 => fun _ : S x0 <> 0 =>
  ex_intro (fun x => S x0 = S x) x0 eq_refl
end).

(*Fact lt_discrim : forall (n m:nat), n < m -> S n <> m -> S n < m.
intros.
destruct H as [|a].
- contradiction.
- unfold lt.
apply le_n_S. exact H.
Qed.

Fact lt_discrim2 : forall (n m:nat), n < S m -> n <> m -> n < m.
intros.
apply le_S_S.
apply lt_discrim.
- exact H.
- injection. exact H0.
Qed.*)

(*- induction (zerop n).
apply le_n_S. exact H.*)
End Numbers.



(** Ugly fact about default implementation of [sub] *)
Theorem sub_non_distrib : exists (x y z : nat), x + (y - z) <> (x + y) - z.
apply (ex_intro _ 1).
apply (ex_intro _ 0).
apply (ex_intro _ 1).
discriminate.
Qed.

Definition option_bind {A B:Type} (o:option A) (k:A -> option B) : option B :=
  match o with
    | None => None
    | Some x => k x
  end.

Definition option_join {A:Type} (o:option (option A)) : option A := 
  option_bind o (fun x => x).

Definition option_join' {A:Type} (o:option (option A)) : option A := match o with
  | None => None
  | Some None => None
  | Some (Some x) => Some x
end.

Definition option_bind' {A B:Type} (o:option A) (k:A -> option B) : option B :=
  option_join' (option_map k o).

Infix ">>=" := option_bind (at level 65).

Notation "x |> f" := (f x)
  (at level 90, left associativity, only parsing).
Notation "f <| x" := (f x)
  (at level 90, left associativity, only parsing).

(* Safe predecessor function *)
Definition s_pred (n:nat) : n <> 0 -> nat.
intro.
destruct n.
* contradiction.
* exact n.
Defined.

Print s_pred.



Fixpoint m4 (n m:nat) (H:m <= n) : nat.
destruct (n) as [|x]; destruct m as [|y].
- exact O.
- apply nle_0 in H. contradiction.
- exact n.
- apply le_S_S in H.
exact (m4 x y H).
Defined.

Notation "n -( H )- m" := (m4 n m H) (at level 50).
(* Notation "n -- m" := (m4 n m _) (at level 50, only printing).
 *)
(** Proof is irrelevant *)
Fact m4_irrelevant (n m:nat) (H1 H2:m <= n) : n -(H1)- m = n -(H2)- m.
rewrite (proof_irrelevance <| m <= n <| H1 <| H2).
reflexivity.
Qed.

Fact m4_n_0 (n:nat) : n -(le_0_n n)- 0 = n.
case n; reflexivity.
Qed.

Fact m3_S2 (n m:nat) (H:m <= n) :
  let H2:(S m <= S n) := (le_S_S m n |> @proj1 _ _) H in
  S n -(H2)- S m = n -(H)- m.
intro.
unfold m4.
fold m4.
apply m4_irrelevant.
Qed.

Lemma S_inj (x y:nat) : S x = S y -> x = y.
intro.
injection H.
trivial.
Qed.

Fact m3_S_n (n m:nat) (H1:m <= n) :
  exists H2,
  S n -(H2)- m = S (n -(H1)- m).
apply (ex_intro _ (le_S_relax_right _ _ H1)).

induction m as [|m1].
- shelve.
- apply S_inj.
simpl. (*applies le_S_S*)
set (HSS := match le_S_S m1 n with
   | conj _ H0 => H0
   end (le_S_relax_right (S m1) n H1)).
rewrite <- IHm1.

Lemma doge (n m:nat) (H1:S m <= n) :
  exists H2,
  n -(H2)- m <> 0.
set (H2 := le_S_relax_left _ _ H1).
apply (ex_intro _ H2).
induction n.
- shelve.
- 
(* destruct H1 as [| x].
- shelve.
- *) 


Fact m3_n_S (n m:nat) (H1:S m <= n) :
  exists H2 H3,
  n -(H1)- S m = s_pred (n -(H2)- m) H3.
set (H2 := le_S_relax_left _ _ H1).
apply (ex_intro _ H2).
assert (H3 : n -(H2)- m <> 0).

(*
Fixpoint m3 (n m:nat) : option nat := 
match n with
| O => match m with
  | O => Some O
  | S _ => None
  end
| S n' => match m with
  | O => Some n
  | S m' => m3 n' m'
  end
end.
*)

Fixpoint m3 (n m:nat) : option nat := match (n, m) with
  | (O, O) => Some O
  | (O, S _) => None
  | (S _, O) => Some n
  | (S n', S m') => m3 n' m'
end.

Notation "n -- m" := (m3 n m) (at level 50).

Fact m3_n_0 (n:nat) : n -- 0 = Some n.
case n; reflexivity.
Qed.

Fact m3_S2 (n m:nat) : n -- m = S n -- S m.
reflexivity.
Qed.

Fact m3_n_n (n:nat) : n -- n = Some 0.
induction n.
- reflexivity.
- rewrite <- m3_S2. assumption.
Qed.

Fact m3_0_n (n:nat) : 0 -- n <> None -> n = 0.
intro.
destruct n.
- reflexivity.
- contradiction H. reflexivity.
Qed.

(* experiments *)

Definition fail_if_0 (n:nat) : option nat :=
  match n with
    | O => None
    | x => Some x
  end.

Definition f2 (on:option nat) : option nat :=
  match on with
    | None
    | Some O => None
    | Some x => Some (S x)
  end.

Definition f2' (on:option nat) : option nat :=
  option_map S (on >>= fail_if_0).

Fact eq_sub (A B:Type) (f:A -> B) (x y:A) : x = y -> f x = f y.
intro.
apply f_equal.
assumption.
Qed.

Fact f2_eq : f2 = f2'.
apply functional_extensionality.
intro.
destruct x; try (destruct n); reflexivity.
Qed.

Definition maybeS : option nat -> option nat := option_map S.

Lemma maybeS_inj (x y: option nat) : maybeS x = maybeS y -> x = y.
intro.
destruct x.
- destruct y.
* compute in H.
f_equal.
injection H.
trivial.
* compute in H. discriminate.
- destruct y.
* compute in H. discriminate.
* reflexivity.
Qed.

Definition safe_unwrap (A:Set) (o:option A) : o <> None -> A :=
  option_rec (fun o0 : option A => o0 <> None -> A)
  (fun (a : A) (_ : Some a <> None) => a)
  (fun H : None <> None => False_rec A (H eq_refl)) o.

Definition safe_unwrap_tactics (A:Set) (o:option A) : o <> None -> A.
elim o; intro.
- intro. exact a.
- contradiction H.
reflexivity.
Defined.

Goal safe_unwrap = safe_unwrap_tactics.
reflexivity.
Qed.

(* Fallible predecessor function *)
Definition maybe_pred_f (n:nat) : option nat :=
  match n with
    | O => None
    | S x => Some x
  end.

Notation "'maybe_pred' o" := (option_bind o maybe_pred_f) (at level 0).

(* Safe predecessor function *)
Definition s_pred (n:nat) : n <> 0 -> nat.
intro.
destruct n.
* contradiction.
* exact n.
Defined.

(* idk if i actually need this lemma *)
Lemma maybe_pred_inj (x y: option nat) :
  x <> Some 0 -> y <> Some 0 -> maybe_pred x = maybe_pred y -> x = y.
intros H1 H2 H3.
destruct x.
- destruct y.
* f_equal.
destruct n.
+ contradiction.
+ destruct n0.
++ contradiction.
++ f_equal. injection H3. trivial.
* destruct n.
+ contradiction. 
+ discriminate.
- destruct y.
* destruct n.
+ contradiction.
+ discriminate.
* reflexivity.
Qed.

Lemma doge (x y:option nat) : y <> (Some 0) -> x = maybe_pred y -> maybeS x = y.
intros H1 H2.
destruct y; rewrite H2.
- destruct n.
* contradiction H1. reflexivity.
* reflexivity.
- reflexivity.
Qed.

(* Lemma doge2 (n m:nat) : n <> m -> n -- m <> Some 0.
intro.
induction n.
- shelve.
- *)

Fact m3_lemma_1_test2 (n m:nat) : (S m) <= n -> n -- S m = maybe_pred (n -- m).
intro.
induction n.
- compute.
destruct m; reflexivity.
- rewrite <- m3_S2.
apply doge in IHn.
shelve.


rewrite <- IHn.
+
destruct m.
* apply nle_0 in H. contradiction.
* rewrite <- m3_S2.
apply le_S in H.
shelve.
+ apply le_S_relax_left. assumption.
Unshelve.
Abort.

(* It's false lol *)
Fact m3_lemma_1_test (n m:nat) : n < m -> n -- S m = maybeS (n -- m).
unfold lt.
intro.
induction n.
- compute.
destruct m.
* apply nle_0 in H. contradiction.
* reflexivity.
- rewrite <- m3_S2.
rewrite (maybeS_inj _ (maybeS (S n -- m))). reflexivity.
rewrite <- IHn.
+
destruct m.
* apply nle_0 in H. contradiction.
* rewrite <- m3_S2.
apply le_S in H.
shelve.
+ apply le_S_relax_left. assumption.
Unshelve.
Abort.


Fact m3_lemma_1_test (n m:nat) : n -- S m = f2 (n -- m).
induction n.
- compute.
case m; reflexivity.
- apply (f_equal f2) in IHn.
all: swap 1 2.
unfold m3 in *.
fold m3 in *.


Fact m3_lemma_1 (n m:nat) : n -- S m <> None -> n -- m <> None.
intro.
induction n.
all: swap 1 2.
unfold m3 in *.
fold m3 in *.


Fact m3_lemma_2 (n m:nat) : n -- m <> None -> m <= n.
intro.
induction m.
all:swap 1 2.
apply le_S4.
apply IHm.

Fact m3_lemma'_1 (n m:nat) : m <= n -> n -- m <> None.
intro.
induction H.
all: swap 1 2.


(*
Fact ok (n m:nat) : n -- m <> None -> S n -- m <> None.
intro.
induction n.
- apply m3_0_n in H.
rewrite H.
discriminate.
- apply IHn.
*)

(*
Fact ok (n m:nat) : n -- m <> None -> S n -- m <> None.
intro.
unfold m3 in *.
fold m3 in *.
set (f2 := match m with
| 0 => Some (S n)
| S m' => n -- m'
end).
refine (fun e => match e in _ = x return False with
  | eq_refl _ => _
end).
(*match m with
  | O => 1
  | S x => 2
end*)
(*match e with
  | eq_refl _ => 1
end*)
elim m.
* discriminate.
* intros.
*)

Fact m3nz (n m:nat) : m <= n -> n -- m <> None.
intro.
induction H.
- rewrite (m3_n_n m). discriminate.
-

(*
Fact m3nz (n m:nat) : m <= n -> n -- m <> None.
intro.
induction m.
- rewrite (m3_n_0 n). discriminate.
- elim H.
* rewrite m3_n_n. discriminate.
* intros.
set (k := m0) in *.
unfold m3.
apply le_S_relax_left in H.
apply IHm in H.

Fact m3nz (n m:nat) : m <= n -> n -- m <> None.
intro.
induction n.
- apply le_n_0_iff_eq_n_0 in H. rewrite H. discriminate.
- induction m.
* rewrite (m3_n_0 (S n)). discriminate.
* 
*)

Theorem sub3_distrib : ~ exists (x y z : nat), x + (y - z) <> (x + y) - z.

(*
zerop
lt_asym
lt_discrim
apply (lt_irrefl 0 H).
apply lt_S_n in H.
*)