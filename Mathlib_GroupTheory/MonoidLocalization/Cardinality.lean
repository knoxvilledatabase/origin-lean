/-
Extracted from GroupTheory/MonoidLocalization/Cardinality.lean
Genuine: 1 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.GroupTheory.MonoidLocalization.Basic
import Mathlib.GroupTheory.OreLocalization.Cardinality

noncomputable section

/-!

# Cardinality of localizations of commutative monoids

This file contains some results on cardinality of localizations.

-/

universe u

open Cardinal

namespace Localization

variable {M : Type u} [CommMonoid M] (S : Submonoid M)

@[to_additive]
theorem cardinalMk_le : #(Localization S) ≤ #M :=
  OreLocalization.cardinalMk_le S

end Localization
