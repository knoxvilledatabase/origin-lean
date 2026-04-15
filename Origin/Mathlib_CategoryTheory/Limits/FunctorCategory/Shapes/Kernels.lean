/-
Extracted from CategoryTheory/Limits/FunctorCategory/Shapes/Kernels.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# (Co)kernels in functor categories
-/

namespace CategoryTheory.Limits

universe u

variable (C : Type*) [Category.{u} C] [HasZeroMorphisms C]

set_option backward.isDefEq.respectTransparency false in

noncomputable def kerIsKernel [HasKernels C] :
    IsLimit (KernelFork.ofι (ker.ι C) (ker.condition C)) :=
  evaluationJointlyReflectsLimits _ fun f ↦ (KernelFork.isLimitMapConeEquiv ..).2 <|
    (kernelIsKernel f.hom).ofIsoLimit <| Fork.ext <| .refl _

set_option backward.isDefEq.respectTransparency false in

noncomputable def cokerIsCokernel [HasCokernels C] :
    IsColimit (CokernelCofork.ofπ (coker.π C) (coker.condition C)) :=
  evaluationJointlyReflectsColimits _ fun f ↦ (CokernelCofork.isColimitMapCoconeEquiv ..).2 <|
    (cokernelIsCokernel f.hom).ofIsoColimit <| Cofork.ext <| .refl _

end CategoryTheory.Limits
