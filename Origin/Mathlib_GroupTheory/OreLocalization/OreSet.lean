/-
Extracted from GroupTheory/OreLocalization/OreSet.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# (Left) Ore sets

This defines left Ore sets on arbitrary monoids.

## References

* https://ncatlab.org/nlab/show/Ore+set

-/

assert_not_exists RelIso

namespace AddOreLocalization

class AddOreSet {R : Type*} [AddMonoid R] (S : AddSubmonoid R) where
  /-- Common summands on the right can be turned into common summands on the left, a weak form of

cancellability. -/

  ore_right_cancel : ∀ (r₁ r₂ : R) (s : S), r₁ + s = r₂ + s → ∃ s' : S, s' + r₁ = s' + r₂

  oreMin : R → S → R

  oreSubtra : R → S → S

  ore_eq : ∀ (r : R) (s : S), oreSubtra r s + r = oreMin r s + s

end AddOreLocalization

namespace OreLocalization

section Monoid
