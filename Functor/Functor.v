Require Import Basics.
Require Import FunctionalExtensionality.
Require Combinators.

Definition id2 {A:Type} (a:A) := a.

Section Functor.
Class Functor (M:Type -> Type) := {
  fmap {A B:Type} : (A -> B) -> M A -> M B;
  funct_id {A:Type} : @fmap A A id2 = id2;
}.
End Functor.

Section Applicative.
Definition ap_type (M:Type -> Type) (A B:Type) := M (A -> B) -> M A -> M B.
Definition liftA2_type (M:Type -> Type) (A B C:Type) := (A -> B -> C) -> M A -> M B -> M C.

Definition liftA2_from_ap {M:Type -> Type} {A B:Type} `{Functor M}
  (ap:ap_type M A B) : forall C, liftA2_type M C A B :=
  fun C => fun f x y => ap (fmap f x) y.

Definition ap_from_liftA2 {M:Type -> Type} {A B:Type} `{Functor M}
  (liftA2:forall C, liftA2_type M C A B) : ap_type M A B :=
  liftA2 _ id2.

Class Applicative (M:Type -> Type) `{Functor M} := {
  pure {A:Type} : A -> M A;
  ap {A B:Type} : ap_type M A B;
  liftA2 {A B C:Type} : liftA2_type M C A B;
  ap_id {A:Type} {m:M A} : ap (pure id2) m = m;
  ap_composition {A B C:Type} {u:M (B -> C)} {v:M (A -> B)} {w:M A} :
    ap (ap (ap (pure compose) u) v) w = ap u (ap v w);
  ap_hom {A B:Type} {f:A -> B} {a:A} : ap (pure f) (pure a) = pure (f a);
  ap_intrchg {A B:Type} {u:M (A -> B)} {y:A} : ap u (pure y) = ap (pure (fun f => f y)) u;
}.
End Applicative.

Section Monad.
Class Monad (M:Type -> Type) `{Applicative M} := {
  bind {A B:Type} : M A -> (A -> M B) -> M B;
  left_id {A B:Type} {a:A} {k: A -> M B} : bind (pure a) k = k a;
  right_id {A:Type} {m:M A} : bind m pure = m;
  associativity {A B C:Type} {m:M A} {k:A -> M B} {h:B -> M C} :
    bind m (fun a => bind (k a) h) = bind (bind m k) h;
  ap_from_bind {A B:Type} {x:M (A -> B)} {y:M A} :
    ap x y = bind x (fun a => bind y (fun b => pure (a b)));
}.

Definition bind_from_join {M:Type -> Type} `{H:Functor M} {A B:Type}
  (join:M (M B) -> M B) : M A -> (A -> M B) -> M B :=
    fun x k => join (@fmap M H _ (M _) k x).
End Monad.

Notation "a <-- m ; e" := (bind m (fun a => e)) (right associativity, at level 60, only parsing).

Section Option.
#[global, refine]
Instance option_functor : Functor option := {
  fmap := fun (A B:Type) (f: A -> B) (m: option A) =>
    match m with
      | Some a => Some (f a)
      | None => None
    end;
}.
Proof.
all: intros; simpl; unfold id2.
apply functional_extensionality.
refine (fun m:option A =>
      match m with
      | Some a => _
      | None => _
      end).
reflexivity.
reflexivity.
Defined.
(* For some reason this instance is not added automatically. Is this a bug? *)
(* Existing Instance option_functor. *)
(* Actually it was removed from DB and section end, since it was #[local] *)


Definition option_liftA2 {A B C:Type} : liftA2_type option C A B :=
    fun f x y => match (x, y) with
      | (Some a, Some b) => Some (f a b)
      | _ => None
    end.

Definition option_ap {A B:Type} : ap_type option A B := ap_from_liftA2 (fun C => option_liftA2).

#[global,refine]
Instance option_applicative : Applicative option := {
  pure _ a := Some a;
  liftA2 A B C := option_liftA2;
  ap A B := option_ap;
}.
Proof.
all: intros; simpl; unfold id2.
- destruct m; reflexivity.
- destruct u; destruct v; destruct w; reflexivity.
- reflexivity.
- destruct u; reflexivity.
Defined.


#[refine]
Instance option_monad : Monad option := {
  bind _ _ x k := match x with
    | Some a => k a
    | None => None
    end;
}.
Proof.
all: intros; simpl; unfold id2.
- reflexivity.
- destruct m; reflexivity.
- destruct m.
  + destruct (k a); reflexivity.
  + reflexivity.
- reflexivity.
Defined.
End Option.

Section MonadTrans.
Inductive StateT (T:Type) (M:Type -> Type) (A:Type) :=
  | StateTC : (T -> M (T * A)%type) -> StateT T M A.
Arguments StateTC {_ _ _}.

Definition runStateT {T:Type} {M:Type -> Type} `{Monad M} {A:Type}
  (m:StateT T M A) : (T -> M (T * A)%type) := match m with
    StateTC f => f
  end.

Definition StateT_pure {T:Type} {M:Type -> Type} `{Monad M} {A:Type} (a:A) : StateT T M A :=
  StateTC (fun s => pure (s, a)).
Definition StateT_bind {T:Type} {M:Type -> Type} `{Monad M} {A B:Type}
  (m:StateT T M A) (k:A -> StateT T M B) : StateT T M B :=
  StateTC (fun s1 =>
    p2 <-- runStateT m s1;
    let s2 := fst p2 in
    let a2 := snd p2 in
    runStateT (k a2) s2).

(*
Class Monad (M:Type -> Type) `{Applicative M} := {
  bind {A B:Type} : M A -> (A -> M B) -> M B;
  left_id {A B:Type} {a:A} {k: A -> M B} : bind (pure a) k = k a;
  right_id {A:Type} {m:M A} : bind m pure = m;
  associativity {A B C:Type} {m:M A} {k:A -> M B} {h:B -> M C} :
    bind m (fun a => bind (k a) h) = bind (bind m k) h;
  ap_from_bind {A B:Type} {x:M (A -> B)} {y:M A} :
    ap x y = bind x (fun a => bind y (fun b => pure (a b)));
}.*)

Ltac StateT_bind_and_pure v :=
unfold StateT_bind; unfold StateT_pure; unfold id2;
try (destruct v); f_equal;
try (apply functional_extensionality); intros;
simpl.

Lemma pair_lemma (A B:Type) (p:A * B) : (fst p, snd p) = p.
destruct p; reflexivity.
Qed.

Lemma StateT_left_id {M:Type -> Type} `{Monad M} {T A B:Type}
  (a:A) (k:A -> StateT T M B)
  : StateT_bind (StateT_pure a) k = k a.
unfold StateT_bind; unfold StateT_pure; unfold id2; simpl.

replace (fun s1 : T =>
  bind (pure (s1, a))
    (fun p2 : T * A => runStateT (k (snd p2)) (fst p2)))
with (fun s1 : T => runStateT (k a) s1).

- destruct (k a); reflexivity.
- apply functional_extensionality; intro; rewrite left_id; reflexivity.
Qed.

Lemma StateT_right_id {M:Type -> Type} `{Monad M} {T A:Type}
  (m:StateT T M A)
  : StateT_bind m StateT_pure = m.
unfold StateT_bind; unfold StateT_pure; unfold id2; simpl.

replace (fun s1 : T =>
  bind (runStateT m s1) (fun p2 : T * A => pure (fst p2, snd p2)))
with (fun s1 : T => runStateT m s1).

- destruct m; reflexivity.
- apply functional_extensionality; intro.
replace (fun p2 : T * A => pure (fst p2, snd p2)) with (@pure _ _ _ (T * A)).
+ rewrite right_id; reflexivity.
+ apply functional_extensionality; intro.
rewrite pair_lemma; reflexivity.
Qed.

Lemma StateT_associativity {M:Type -> Type} `{Monad M} {T A B C:Type}
  (m:StateT T M A) (k:A -> StateT T M B) (h:B -> StateT T M C) :
    StateT_bind m (fun a => StateT_bind (k a) h) = StateT_bind (StateT_bind m k) h.
unfold StateT_bind; unfold StateT_pure; unfold id2; simpl.
f_equal. apply functional_extensionality; intro.
rewrite associativity; reflexivity.
Qed.



#[refine]
Instance StateT_functor (T:Type) (M:Type -> Type) `{Monad M} : Functor (StateT T M) := {
  fmap A B f m := StateT_bind m (fun a => StateT_pure (f a));
}.
all: intros; simpl; unfold id2.
unfold StateT_bind.
apply functional_extensionality; intro.
destruct x; f_equal.
simpl.
apply functional_extensionality; intro.
assert ((fun p2 : T * A => pure (fst p2, snd p2)) = pure) as f_is_pure.
- apply functional_extensionality; intro.
rewrite pair_lemma.
reflexivity.
- rewrite f_is_pure.
apply right_id.
Defined.

Definition StateT_liftA2 {T A B C:Type} {M:Type -> Type} `{Monad M}
  : liftA2_type (StateT T M) C A B
  := fun f x y =>
    StateT_bind x (fun a =>
    StateT_bind y (fun b =>
    StateT_pure (f a b))).

Definition StateT_ap {T A B:Type} {M:Type -> Type} `{Monad M}
  : ap_type (StateT T M) A B
  := ap_from_liftA2 (fun C => StateT_liftA2).

#[refine]
Instance StateT_applicative (T:Type) (M:Type -> Type) `{Monad M} : Applicative (StateT T M) := {
  pure A := StateT_pure;
  liftA2 A B C := StateT_liftA2;
  ap A B := StateT_ap;
}.

(* TODO: write proofs of monadic laws and then use them in
proof of applicative laws *)

all: intros;
unfold StateT_ap; unfold ap_from_liftA2; unfold StateT_liftA2;
(*unfold StateT_bind; unfold StateT_pure;*)
unfold id2; simpl.

all: try (destruct m); f_equal;
try (apply functional_extensionality); intros; simpl.

all: try (rewrite left_id); simpl.

all: unfold runStateT; simpl.

Abort.


End MonadTrans.

Require Extraction.

Extraction Language Scheme.
Recursive Extraction ap.
Recursive Extraction option_applicative.