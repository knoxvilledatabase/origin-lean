/-
Extracted from RingTheory/Localization/Away/Basic.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Localizations away from an element

## Main definitions

* `IsLocalization.Away (x : R) S` expresses that `S` is a localization away from `x`, as an
  abbreviation of `IsLocalization (Submonoid.powers x) S`.
* `exists_reduced_fraction' (hb : b ≠ 0)` produces a reduced fraction of the form `b = a * x^n` for
  some `n : ℤ` and some `a : R` that is not divisible by `x`.

## Implementation notes

See `Mathlib/RingTheory/Localization/Basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/

section CommSemiring

variable {R : Type*} [CommSemiring R] (M : Submonoid R) {S : Type*} [CommSemiring S]

variable [Algebra R S] {P : Type*} [CommSemiring P]

namespace IsLocalization

section Away

variable (x : R)

abbrev Away (S : Type*) [CommSemiring S] [Algebra R S] :=
  IsLocalization (Submonoid.powers x) S

namespace Away

variable [IsLocalization.Away x S]

noncomputable def invSelf : S :=
  mk' S (1 : R) ⟨x, Submonoid.mem_powers _⟩
