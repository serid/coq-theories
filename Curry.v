(*H*)

Require Import List.
Import ListNotations.

Fixpoint typelist_to_tuple (t : list Set) : Set := match t with
| x :: [] => x
| x :: r => (x * typelist_to_tuple r)
| [] => True
end.

Fixpoint typelist_to_arrows (t : list Set) : Set := match t with
| x :: [] => x
| x :: r => x -> typelist_to_arrows r
| [] => True
end.

Definition nat_recursion (A : Type) (z : A) (s : A -> A) (n : nat) : A
  := nat_rect (fun _ => A) z (fun _ => s) n.

Definition with_n_arrows (A : Type) (n : nat) : Type :=
  nat_recursion Type A (fun t => Type -> t) n.

Check nat_rect.

Definition collect_n_args {A : Type} (n : nat)
  (continuation : list Type -> A) : with_n_arrows A n :=
let fix collect_n_args' (n : nat) (types : list Type) : with_n_arrows A n
  := match n with
  | O => continuation types
  | S n1 => fun (t : Type) => collect_n_args' n1 (t :: types)
  end
in collect_n_args' n [].


Fixpoint n_to_foralls' (n : nat) (types : list Set)
  (continuation : list Set -> Type) : Type := match n with
| O => continuation (rev types)
| S n1 => forall x, n_to_foralls' n1 (x :: types) continuation
end.

Definition n_to_foralls (n : nat) (continuation : list Set -> Type) : Type
  := n_to_foralls' n [] continuation.


(* Type of curry_n *)
Definition curry_n_t (n : nat) : Type := n_to_foralls n
  (fun types => forall r : Set,
    (typelist_to_tuple types -> r) -> typelist_to_arrows (app types [r])).

Print curry.

Fixpoint curry_n (n : nat) (types : list Type) : _ := match n with
| O => I
| S n1 => 
end.

Compute (curry_n_t 3).

(* Semantics of curry_n *)
Definition curry_n (n : nat) : curry_n_t n :=
  let body := fun types f =>
    _ in
  collect_n_args n body.
