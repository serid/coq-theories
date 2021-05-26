Class MatchType (A:Type) := {
  match_type : nat;
}.

Instance mt_unit : MatchType unit := {
  match_type := 0;
}.

Instance mt_fun : MatchType (bool -> bool) := {
  match_type := 1;
}.

Instance mt_nat : MatchType nat := {
  match_type := 2;
}.
Arguments match_type (_) {_}.

Inductive Matchable :=
  matchable : forall A, MatchType A -> Matchable
.
Arguments matchable (_) {_}.

Definition matchable_match_type (x:Matchable) := match x with
  | @matchable A mt => @match_type A mt
end.

Compute (matchable_match_type (matchable unit)).
Compute (matchable_match_type (matchable (bool -> bool))).
Compute (matchable_match_type (matchable nat)).