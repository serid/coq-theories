Require Import Tactics.

Class Monoid (A : Type) := {
  mzero : A;
}.

Class Arrow (Arr : Type) (O : Type) := {
  domain : Arr -> O;
  codomain : Arr -> O;
}.

Definition aux (Arr : Type) {O : Type} `{Arrow Arr O} a b :=
  {arr : Arr | domain arr = a /\ codomain arr = b}.


Class Cat (Objects Hom:Type) := {
  instance : Arrow Hom Objects;

  comp : forall {a b c}, aux Hom a b -> aux Hom b c -> aux Hom a c;
  ident : forall {a}, aux Hom a a;
}.

Class CatLaws {Objects Hom:Type} (c_:Cat Objects Hom) := {
  assoc : forall (a b c d:Objects) (f:aux Hom a b) (g:aux Hom b c) (h:aux Hom c d),
    comp (comp f g) h = comp f (comp g h);

  ident_comp_left : forall a x (f:aux Hom a x), comp f ident = f;
  ident_comp_right : forall x b (g:aux Hom x b), comp ident g = g;
}.


Inductive CatOfNat : Type :=
| aNatObject.

Lemma singleton_cat_of_nat (x:CatOfNat) : x = aNatObject.
destruct x. reflexivity.
Qed.

Lemma all_cats_of_nat_eq (x y:CatOfNat) : x = y.
destruct x. destruct y. reflexivity.
Qed.

Instance hh : Arrow (nat -> nat) CatOfNat := {|
  domain _ := aNatObject;
  codomain _ := aNatObject;
|}.

#[refine]
Instance catNatSumMonoid : Cat CatOfNat (nat -> nat) := {|
  instance := hh;
|}.
(* comp *)
{
  intros.
  rename X into f.
  rename X0 into g.
  unfold aux in *.
  apply proj1_sig in f.
  apply proj1_sig in g.

  assert (result := fun x => g (f x)).
  refine (exist _ result _).

  split; apply all_cats_of_nat_eq.
}

(* ident *)
{
  intros.
  unfold aux.
  assert (result := fun x:nat => x).
  refine (exist _ result _).

  split; apply all_cats_of_nat_eq.
}
Defined.

Instance catNatSumMonoidLaws : CatLaws catNatSumMonoid.
apply Build_CatLaws.
{
  intros.
  f_equal.
  simpl.
}

Print CatNatSumMonoid.