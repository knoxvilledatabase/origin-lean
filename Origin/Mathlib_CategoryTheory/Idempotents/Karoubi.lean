/-
Extracted from CategoryTheory/Idempotents/Karoubi.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The Karoubi envelope of a category

In this file, we define the Karoubi envelope `Karoubi C` of a category `C`.

## Main constructions and definitions

- `Karoubi C` is the Karoubi envelope of a category `C`: it is an idempotent
  complete category. It is also preadditive when `C` is preadditive.
- `toKaroubi C : C ⥤ Karoubi C` is a fully faithful functor, which is an equivalence
  (`toKaroubiIsEquivalence`) when `C` is idempotent complete.

-/

noncomputable section

open CategoryTheory.Category CategoryTheory.Preadditive CategoryTheory.Limits

namespace CategoryTheory

variable (C : Type*) [Category* C]

namespace Idempotents

structure Karoubi where
  /-- an object of the underlying category -/
  X : C
  /-- an endomorphism of the object -/
  p : X ⟶ X
  /-- the condition that the given endomorphism is an idempotent -/
  idem : p ≫ p = p := by cat_disch

namespace Karoubi

variable {C}

attribute [reassoc (attr := simp)] idem
