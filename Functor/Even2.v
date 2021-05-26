Require Import Coq.Arith.PeanoNat.

(* is_even and is_odd (recursive definition) *)
Fixpoint
  is_odd (n:nat) : bool :=
  match n with
  | 0 => false
  | S x => is_even x
  end

  with

  is_even (n:nat) : bool := 
  match n with
  | 0 => true
  | S x => is_odd x
  end.

(* if n is odd, it is not even *)
Theorem odd_is_not_even :
  forall n, (is_odd n = true) -> (is_even n = false).
intros.
replace false with (negb true) by reflexivity.
rewrite <- H.
clear H.
induction n.
- reflexivity.
- simpl. rewrite IHn. destruct (is_odd n); reflexivity.
Qed.