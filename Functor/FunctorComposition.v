Require Import Basics.

Require Import Functor.

Print Functor.

Section FunctorComposition.
Infix "<<" := compose (at level 60).
Fact compose_illustration (A B C:Type) : (A -> B) -> (B -> C) -> (A -> C).
exact (fun (f:A -> B) (g:B -> C) => (g << f)).
Qed.

Section FunctorEquality.
Variable (F:Type -> Type).
Variables (inst1 inst2:Functor F).
Definition fmap1 : forall {A B:Type}, (A -> B) -> F A -> F B := @fmap F inst1.
Definition fmap2 : forall {A B:Type}, (A -> B) -> F A -> F B := @fmap F inst2.

(* TODO: encode Parametricity theory in FreeTheorem.v and derive this hypothesis *)
Axiom free_theorem_for_fmap : forall (A B1 B2 C:Type)
  (f:A -> B1) (g:B2 -> C) (h:A -> B2) (k:B1 -> C),
  (g << h) = (k << f) ->
    ((fmap2 g) << (fmap1 h)) =
      ((fmap1 k) << (fmap2 f)).

Lemma lemma1 {X Y:Type} : @fmap1 X Y = @fmap2 X Y.
apply functional_extensionality.
intros.
rewrite <- Combinators.compose_id_left.
rewrite <- (@funct_id F inst1).
(*enough (A:Type).
enough (B1:Type).
enough (B2:Type).
enough (C:Type).*)
(*unfold fmap1.
fold (@fmap1 X Y).*)
rewrite <- (free_theorem_for_fmap _ _ _ _  _ id2 x _).
rewrite -> (@funct_id F inst2).
rewrite -> Combinators.compose_id_left.
reflexivity.
reflexivity.
Qed.
End FunctorEquality.

Lemma lemma2 {X Y Z:Type} (f:Y -> Z) (g:X -> Y) : (f << g) = (id2 << (f << g)).
set (k := f << g).
symmetry.
apply Combinators.compose_id_left.
Qed.

Theorem funct_composition (m:Type -> Type) (inst:Functor m)
  (A B C:Type)
  (f:B -> C) (g:A -> B) : fmap (f << g) = (fmap f) << (fmap g).
set (He := free_theorem_for_fmap m inst inst _ _ _ _  (f << g) f g id2).
unfold fmap1 in He.
unfold fmap2 in He.
rewrite -> He.
- rewrite -> (@funct_id _ _).
rewrite -> Combinators.compose_id_left.
reflexivity.
- rewrite -> Combinators.compose_id_left.
reflexivity.
Qed.
End FunctorComposition.