(*Inductive eq2 (A:Type) (x:A) : A -> Prop :=
    eq_refl2 : eq2 A x x.*)

Inductive eq2 (A:Type) : A -> A -> Prop :=
    eq_refl2 : forall (x:A), eq2 A x x.

Definition eq_symm (A:Type) (x y:A) (H:eq x y) : eq y x :=
match H in eq _ z return eq z x with
| eq_refl _ => eq_refl x
end.

Print eq_ind.
Print eq_sym.

Print eq.