Class Semigroup (m : Type) := {
  mplus : m -> m -> m;
}.

Class Monoid (m : Type) `{Semigroup m} := {
  mzero : m;
}.

Infix "<>" := mplus.

Instance nat_plus_sem : Semigroup nat := {
  mplus := plus;
}.

Instance nat_plus_mon : @Monoid nat nat_plus_sem := {
  mzero := 0;
}.

Instance nat_mul_sem : Semigroup nat := {
  mplus := mult;
}.

Instance nat_mul_mon : @Monoid nat nat_mul_sem := {
  mzero := 1;
}.

Set Typeclasses Debug.

Definition test := @mplus _ nat_mul_sem mzero mzero.
Definition test2 {A:Set} `{Monoid A} (x:A) := mplus x mzero.


Require Extraction.

Recursive Extraction test2.