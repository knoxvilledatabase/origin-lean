/-
Extracted from Algebra/CharP/Frobenius.lean
Genuine: 4 of 6 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
### The Frobenius endomorphism

## Tags

Frobenius endomorphism

## Implementation notes

The definitions of `frobenius` and `iterateFrobenius` ring homomorphisms are in
`Mathlib/Algebra/CharP/Lemmas.lean` as they are needed for some results that in turn are used in
files forbidding to import algebra-related definitions (see `Mathlib/Algebra/CharP/Two.lean`).
-/

section CommSemiring

variable {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S]

variable (f : R →* S) (g : R →+* S) (p m n : ℕ) [ExpChar R p] [ExpChar S p] (x y : R)

lemma iterate_frobenius : (frobenius R p)^[n] x = x ^ p ^ n := congr_fun (pow_iterate p n) x

variable (R)

lemma iterateFrobenius_eq_pow : iterateFrobenius R p n = frobenius R p ^ n := by
  ext; simp [iterateFrobenius_def, iterate_frobenius]

lemma coe_iterateFrobenius : iterateFrobenius R p n = (frobenius R p)^[n] :=
  (pow_iterate p n).symm

lemma iterateFrobenius_one_apply : iterateFrobenius R p 1 x = x ^ p := by
  rw [iterateFrobenius_def, pow_one]
