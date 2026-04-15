/-
Extracted from Algebra/Homology/HomotopyCategory/MappingCocone.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The mapping cocone

Given a morphism `φ : K ⟶ L` of cochain complexes, the mapping cone
allows to obtain a triangle `K ⟶ L ⟶ mappingCone φ ⟶ ...`. In this
file, we define the mapping cocone, which fits in a rotated triangle:
`mappingCocone φ ⟶ K ⟶ L ⟶ ...`.

-/

open CategoryTheory Limits HomologicalComplex Pretriangulated

namespace CochainComplex

open HomComplex

variable {C : Type*} [Category* C] [Preadditive C]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

noncomputable def mappingCocone [HasHomotopyCofiber φ] :
    CochainComplex C ℤ := (mappingCone φ)⟦(-1 : ℤ)⟧

namespace mappingCocone

variable [HasHomotopyCofiber φ]

noncomputable def fst : mappingCocone φ ⟶ K :=
  -((mappingCone.fst φ).leftShift (-1) 0 (add_neg_cancel 1)).homOf

noncomputable def snd : Cochain (mappingCocone φ) L (-1) :=
  (mappingCone.snd φ).leftShift (-1) (-1) (zero_add _)

noncomputable def inl : Cochain K (mappingCocone φ) 0 :=
  (mappingCone.inl φ).rightShift (-1) 0 (zero_add _)

noncomputable def inr : Cocycle L (mappingCocone φ) 1 :=
  (Cocycle.ofHom (mappingCone.inr φ)).rightShift (-1) 1 (by lia)

set_option backward.isDefEq.respectTransparency false in
