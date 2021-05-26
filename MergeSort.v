Require Nat.

Require Import List.
Import ListNotations.

Fixpoint last_error {A:Type} (ls:list A) : option A := match ls with
  | [] => None
  | [a] => Some a
  | a :: tl => last_error tl
end.

#[program]
Fixpoint get_last {A:Type} (ls:list A) (H:ls <> []) : A :=
match ls with
  | [] => _
  | a :: tl =>
  match tl with
    | [] => a
    | b :: tl2 => get_last tl _
  end
end.
Print get_last.

(* Same function but without #[program] *)
Lemma stuff {A:Type} (a:A) (ls tl:list A) : a :: tl = ls -> ls <> [].
intro.
intro.
rewrite H0 in H.
inversion H.
Qed.
Fixpoint get_last_full {A:Type} (ls:list A) (H:ls <> []) : A :=
match ls return ls <> [] -> A with
  | [] => fun H => False_rect A (H eq_refl)
  | a :: tl => fun _ =>
  match tl as tl' return tl' = tl -> A with
    | [] => fun _ => a
    | b :: tl2 => fun H => get_last_full tl (stuff b tl tl2 H)
  end eq_refl
end H.

Inductive SortedVec {A:Type} (le:A -> A -> Prop) : list A -> Type :=
  | sv_empty : SortedVec le []
  | sv_singleton : forall a, SortedVec le [a]
  | sv_cons : forall b ls (H:ls <> []), SortedVec le ls ->
     le (get_last ls H) b -> SortedVec le (b :: ls)
.

Fixpoint merge {A:Type} (le:A -> A -> bool) (l1 l2:list A) :=
  match (l1, l2) with
    | ([], _) => l2
    | (_, []) => l1
    | (a :: t1, b :: t2) =>
      if le a b
      then a :: merge le t1 l2
      else b :: merge le l1 t2
  end.

(* Search (nat -> nat -> bool).
 *)
Compute (merge Nat.leb [] [1; 3; 5] [2; 8]).