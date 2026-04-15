/-
Extracted from Algebra/Homology/TotalComplexSymmetry.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-! The symmetry of the total complex of a bicomplex

Let `K : HomologicalComplex₂ C c₁ c₂` be a bicomplex. If we assume both
`[TotalComplexShape c₁ c₂ c]` and `[TotalComplexShape c₂ c₁ c]`, we may form
the total complex `K.total c` and `K.flip.total c`.

In this file, we show that if we assume `[TotalComplexShapeSymmetry c₁ c₂ c]`,
then there is an isomorphism `K.totalFlipIso c : K.flip.total c ≅ K.total c`.

Moreover, if we also have `[TotalComplexShapeSymmetry c₂ c₁ c]` and that the signs
are compatible `[TotalComplexShapeSymmetrySymmetry c₁ c₂ c]`, then the isomorphisms
`K.totalFlipIso c` and `K.flip.totalFlipIso c` are inverse to each other.

-/

assert_not_exists Ideal TwoSidedIdeal

open CategoryTheory Category Limits

namespace HomologicalComplex₂

variable {C I₁ I₂ J : Type*} [Category* C] [Preadditive C]
    {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} (K : HomologicalComplex₂ C c₁ c₂)
    (c : ComplexShape J) [TotalComplexShape c₁ c₂ c] [TotalComplexShape c₂ c₁ c]
    [TotalComplexShapeSymmetry c₁ c₂ c]

-- INSTANCE (free from Core): [K.HasTotal

lemma flip_hasTotal_iff : K.flip.HasTotal c ↔ K.HasTotal c := by
  constructor
  · intro
    change K.flip.flip.HasTotal c
    have := TotalComplexShapeSymmetry.symmetry c₁ c₂ c
    infer_instance
  · intro
    infer_instance

variable [K.HasTotal c] [DecidableEq J]

attribute [local simp] smul_smul

set_option backward.isDefEq.respectTransparency false in

noncomputable def totalFlipIsoX (j : J) : (K.flip.total c).X j ≅ (K.total c).X j where
  hom := K.flip.totalDesc (fun i₂ i₁ h => ComplexShape.σ c₁ c₂ c i₁ i₂ • K.ιTotal c i₁ i₂ j (by
    rw [← ComplexShape.π_symm c₁ c₂ c i₁ i₂, h]))
  inv := K.totalDesc (fun i₁ i₂ h => ComplexShape.σ c₁ c₂ c i₁ i₂ • K.flip.ιTotal c i₂ i₁ j (by
    rw [ComplexShape.π_symm c₁ c₂ c i₁ i₂, h]))
  hom_inv_id := by ext; simp
  inv_hom_id := by ext; simp

set_option backward.isDefEq.respectTransparency false in
