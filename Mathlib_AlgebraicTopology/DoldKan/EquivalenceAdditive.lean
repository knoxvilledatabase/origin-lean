/-
Extracted from AlgebraicTopology/DoldKan/EquivalenceAdditive.lean
Genuine: 3 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.AlgebraicTopology.DoldKan.NCompGamma

noncomputable section

/-! The Dold-Kan equivalence for additive categories.

This file defines `Preadditive.DoldKan.equivalence` which is the equivalence
of categories `Karoubi (SimplicialObject C) ≌ Karoubi (ChainComplex C ℕ)`.

(See `Equivalence.lean` for the general strategy of proof of the Dold-Kan equivalence.)

-/

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

  CategoryTheory.Idempotents AlgebraicTopology.DoldKan

variable {C : Type*} [Category C] [Preadditive C]

namespace CategoryTheory

namespace Preadditive

namespace DoldKan

@[simp]
def N : Karoubi (SimplicialObject C) ⥤ Karoubi (ChainComplex C ℕ) :=
  N₂

variable [HasFiniteCoproducts C]

@[simp]
def Γ : Karoubi (ChainComplex C ℕ) ⥤ Karoubi (SimplicialObject C) :=
  Γ₂

@[simps]
def equivalence : Karoubi (SimplicialObject C) ≌ Karoubi (ChainComplex C ℕ) where
  functor := N
  inverse := Γ
  unitIso := Γ₂N₂
  counitIso := N₂Γ₂
  functor_unitIso_comp P := by
    let α := N.mapIso (Γ₂N₂.app P)
    let β := N₂Γ₂.app (N.obj P)
    symm
    change 𝟙 _ = α.hom ≫ β.hom
    rw [← Iso.inv_comp_eq, comp_id, ← comp_id β.hom, ← Iso.inv_comp_eq]
    exact AlgebraicTopology.DoldKan.identity_N₂_objectwise P

end DoldKan

end Preadditive

end CategoryTheory
