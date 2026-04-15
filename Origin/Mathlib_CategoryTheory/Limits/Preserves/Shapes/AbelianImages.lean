/-
Extracted from CategoryTheory/Limits/Preserves/Shapes/AbelianImages.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Preservation of coimage-image comparisons

If a functor preserves kernels and cokernels, then it preserves abelian images, abelian coimages
and coimage-image comparisons.
-/

noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory Limits

namespace CategoryTheory.Abelian

variable {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C]

variable {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D]

variable (F : C ⥤ D) [F.PreservesZeroMorphisms]

variable {X Y : C} (f : X ⟶ Y)

section Images

variable [HasCokernel f] [HasKernel (cokernel.π f)] [PreservesColimit (parallelPair f 0) F]
  [PreservesLimit (parallelPair (cokernel.π f) 0) F] [HasCokernel (F.map f)]
  [HasKernel (cokernel.π (F.map f))]

def PreservesImage.iso : F.obj (Abelian.image f) ≅ Abelian.image (F.map f) :=
  PreservesKernel.iso F _ ≪≫ kernel.mapIso _ _ (Iso.refl _) (PreservesCokernel.iso F _) (by simp)
