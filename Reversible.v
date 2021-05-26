Require Import ZArith.
Require Import Ring.

Require Import Basics.

Theorem plus_inverse_left (x y : _) : x = (x + y - y)%Z.
ring.
Qed.

Theorem plus_inverse_right (x y : _) : y = (x + y - x)%Z.
ring.
Qed.

Print plus_inverse_left.

Definition Image {A B} (func : A -> B) :=
  {y : B | exists x : A, y = func x}.

Program Definition makeImage {A B} (func : A -> B) (x : A) : Image func.
refine (exist _ _ _).
eauto.
Unshelve.
assumption.
Defined.

Definition unwrapImage {A B} {func : A -> B} (img: Image func) := proj1_sig img.

Theorem compose_image_weaken {A B C} {g : B -> C} {f : A -> B}
  : Image (compose g f) -> Image g.
intro.
destruct X.
refine (exist _ x _).
destruct e.
unfold compose in H.
refine (ex_intro _ _ _).
exact H.
Defined.

Theorem lemma_zwei : 

(* This bijection only requires
bwd to be a left inverse of fwd.

Equivalently, fwd must be injective and bwd
only has to be injective respectively to the image of fwd. *)
Record LeftBijection (A B : Type) := {
  fwd : A -> B;
  bwd : Image fwd -> A;
  left_inv : forall x, bwd (makeImage fwd x) = x
}.
Arguments fwd {_ _}.
Arguments bwd {_ _}.
Arguments left_inv {_ _}.
Notation "x <->> y" := (LeftBijection x y)
  (at level 99, right associativity, y at level 200).
(*Infix "<->>" := LeftBijection (at level 10).*)

Program Definition plus_right : Z -> Z <->> Z := fun x => {|
  fwd y := (x + y)%Z;
  bwd z := (z - x)%Z;
|}.
Next Obligation.
symmetry.
apply plus_inverse_right.
Defined.

Program Definition plus_left : Z <->> Z -> Z := {|
  fwd := Z.add;
  bwd img := unwrapImage img 0%Z;
|}.
Next Obligation.
destruct x; reflexivity.
Defined.

(* Idk what this means *)
Program Definition plus_inv : Z <->> Z <->> Z := {|
  fwd x := {|
    fwd y := (x + y)%Z;
    bwd z := (z - x)%Z;
  |};
  bwd img := (unwrapImage img).(fwd) 0%Z;
|}.
Next Obligation.
symmetry.
apply plus_inverse_right.
Qed.
Next Obligation.
destruct x; reflexivity.
Qed.

Program Definition comp_inv {A B C} (f : A <->> B) (g : B <->> C)
  : A <->> C := {|
  fwd := compose g.(fwd) f.(fwd);
  bwd := _;
|}.
Next Obligation.
Check (f.(left_inv)).
(* apply (compose_image_weaken) in X. *)
refine (f.(bwd) _).
(* Stash this doge for later *)
set (fwd_g := compose_image_weaken X).
refine (exist _ (g.(bwd) fwd_g) _).
refine (ex_intro _ _ _).
rewrite <- (left_inv g (fwd f _)).
f_equal.
(* apply lemma_zwei *)



destruct X.
unfold compose in *.
destruct e.
refine (ex_intro _ x0 _).
exact H.

Next Obligation.
symmetry.
apply plus_inverse_right.
Defined.
