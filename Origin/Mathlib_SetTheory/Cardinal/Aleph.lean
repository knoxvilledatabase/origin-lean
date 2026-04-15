/-
Extracted from SetTheory/Cardinal/Aleph.lean
Genuine: 5 of 6 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Omega, aleph, and beth functions

This file defines the `ω`, `ℵ`, and `ℶ` functions which enumerate certain kinds of ordinals and
cardinals. Each is provided in two variants: the standard versions which only take infinite values,
and "preliminary" versions which include finite values and are sometimes more convenient.

* The function `Ordinal.preOmega` enumerates the initial ordinals, i.e. the smallest ordinals with
  any given cardinality. Thus `preOmega n = n`, `preOmega ω = ω`, `preOmega (ω + 1) = ω₁`, etc.
  `Ordinal.omega` is the more standard function which skips over finite ordinals.
* The function `Cardinal.preAleph` is an order isomorphism between ordinals and cardinals. Thus
  `preAleph n = n`, `preAleph ω = ℵ₀`, `preAleph (ω + 1) = ℵ₁`, etc. `Cardinal.aleph` is the more
  standard function which skips over finite cardinals.
* The function `Cardinal.preBeth` is the unique normal function with `beth 0 = 0` and
  `beth (succ o) = 2 ^ beth o`. `Cardinal.beth` is the more standard function which skips over
  finite cardinals.

## Notation

The following notations are scoped to the `Ordinal` namespace.

- `ω_ o` is notation for `Ordinal.omega o`. `ω₁` is notation for `ω_ 1`.

The following notations are scoped to the `Cardinal` namespace.

- `ℵ_ o` is notation for `aleph o`. `ℵ₁` is notation for `ℵ_ 1`.
- `ℶ_ o` is notation for `beth o`. The value `ℶ_ 1` equals the continuum `𝔠`, which is defined in
  `Mathlib/SetTheory/Cardinal/Continuum.lean`.
-/

assert_not_exists Field Finsupp Module Cardinal.mul_eq_self

noncomputable section

open Function Set Cardinal Equiv Order Ordinal

universe u v w

/-! ### Omega ordinals -/

namespace Ordinal

def IsInitial (o : Ordinal) : Prop :=
  o.card.ord = o

theorem IsInitial.le_ord_iff_card_le {o : Ordinal} (ho : o.IsInitial) (c : Cardinal) :
    o ≤ c.ord ↔ o.card ≤ c := by
  grw [← ord_le_ord, ho.ord_card]

theorem IsInitial.card_le_card {a b : Ordinal} (ha : IsInitial a) : a.card ≤ b.card ↔ a ≤ b := by
  refine ⟨fun h ↦ ?_, Ordinal.card_le_card⟩
  rw [← ha.le_ord_iff_card_le] at h
  grw [h, ord_card_le]

theorem IsInitial.card_lt_card {a b : Ordinal} (hb : IsInitial b) : a.card < b.card ↔ a < b :=
  lt_iff_lt_of_le_iff_le hb.card_le_card

theorem isInitial_ord (c : Cardinal) : IsInitial c.ord := by
  rw [IsInitial, card_ord]
