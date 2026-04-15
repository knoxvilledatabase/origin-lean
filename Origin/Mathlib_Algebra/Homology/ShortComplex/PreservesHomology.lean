/-
Extracted from Algebra/Homology/ShortComplex/PreservesHomology.lean
Genuine: 6 of 8 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Functors which preserves homology

If `F : C ⥤ D` is a functor between categories with zero morphisms, we shall
say that `F` preserves homology when `F` preserves both kernels and cokernels.
This typeclass is named `[F.PreservesHomology]`, and is automatically
satisfied when `F` preserves both finite limits and finite colimits.

If `S : ShortComplex C` and `[F.PreservesHomology]`, then there is an
isomorphism `S.mapHomologyIso F : (S.map F).homology ≅ F.obj S.homology`, which
is part of the natural isomorphism `homologyFunctorIso F` between the functors
`F.mapShortComplex ⋙ homologyFunctor D` and `homologyFunctor C ⋙ F`.

-/

namespace CategoryTheory

open Category Limits

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]

namespace Functor

variable (F : C ⥤ D)

class PreservesHomology (F : C ⥤ D) [PreservesZeroMorphisms F] : Prop where
  /-- the functor preserves kernels -/
  preservesKernels ⦃X Y : C⦄ (f : X ⟶ Y) : PreservesLimit (parallelPair f 0) F := by
    infer_instance
  /-- the functor preserves cokernels -/
  preservesCokernels ⦃X Y : C⦄ (f : X ⟶ Y) : PreservesColimit (parallelPair f 0) F := by
    infer_instance

variable [PreservesZeroMorphisms F]

lemma PreservesHomology.preservesKernel [F.PreservesHomology] {X Y : C} (f : X ⟶ Y) :
    PreservesLimit (parallelPair f 0) F :=
  PreservesHomology.preservesKernels _

lemma PreservesHomology.preservesCokernel [F.PreservesHomology] {X Y : C} (f : X ⟶ Y) :
    PreservesColimit (parallelPair f 0) F :=
  PreservesHomology.preservesCokernels _

-- INSTANCE (free from Core): preservesHomologyOfExact

end Functor

namespace ShortComplex

variable {S S₁ S₂ : ShortComplex C}

namespace LeftHomologyData

variable (h : S.LeftHomologyData) (F : C ⥤ D)

class IsPreservedBy [F.PreservesZeroMorphisms] : Prop where
  /-- the functor preserves the kernel of `S.g : S.X₂ ⟶ S.X₃`. -/
  g : PreservesLimit (parallelPair S.g 0) F
  /-- the functor preserves the cokernel of `h.f' : S.X₁ ⟶ h.K`. -/
  f' : PreservesColimit (parallelPair h.f' 0) F

variable [F.PreservesZeroMorphisms]

-- INSTANCE (free from Core): isPreservedBy_of_preservesHomology

variable [h.IsPreservedBy F]

include h in

lemma IsPreservedBy.hg : PreservesLimit (parallelPair S.g 0) F :=
  @IsPreservedBy.g _ _ _ _ _ _ _ h F _ _

lemma IsPreservedBy.hf' : PreservesColimit (parallelPair h.f' 0) F := IsPreservedBy.f'

set_option backward.isDefEq.respectTransparency false in
