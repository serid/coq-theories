From Coq Require Extraction.

Inductive vec (A : Type) : nat -> Type :=
  | vnil : vec A 0
  | vcons : forall len, A -> vec A len -> vec A (1 + len).

Arguments vnil {A}%type_scope.
Arguments vcons {A}%type_scope _ _ _.

Fixpoint yo (n : nat) : vec bool n := match n with
  | O => vnil
  | S x => vcons _ false (yo x) end.

Recursive Extraction yo.

Definition tail {A} n (v: vec A (S n)) :=
  match v in vec _ (S m) return vec _ m with
  | vnil => 0
  | vcons n' a y => y
  end.

Recursive Extraction tail.


Definition o (n:nat) (y:unit) : n = n := eq_refl.
Arguments o {_} _.
Definition o2 : unit -> 1 = 1 := o.
Arguments o [_] _.
Fail Definition o3 : unit -> 1 = 1 := o.