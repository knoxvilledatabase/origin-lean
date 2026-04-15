/-
Extracted from RingTheory/OreLocalization/Cardinality.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.GroupTheory.OreLocalization.Cardinality
import Mathlib.RingTheory.OreLocalization.Ring

/-!
# Cardinality of Ore localizations of rings

This file contains some results on cardinality of Ore localizations of rings.
-/

universe u

open Cardinal

namespace OreLocalization

variable {R : Type u} [Ring R] {S : Submonoid R} [OreLocalization.OreSet S]

theorem cardinalMk (hS : S ≤ nonZeroDivisorsRight R) : #(OreLocalization S R) = #R :=
  le_antisymm (cardinalMk_le S) (mk_le_of_injective (numeratorHom_inj hS))

end OreLocalization
