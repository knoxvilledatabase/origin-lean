/-
Extracted from Algebra/Category/ModuleCat/Abelian.lean
Genuine: 2 | Conflates: 0 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Abelian.Basic

/-!
# The category of left R-modules is abelian.

Additionally, two linear maps are exact in the categorical sense iff `range f = ker g`.
-/

open CategoryTheory

open CategoryTheory.Limits

noncomputable section

universe w v u

namespace ModuleCat

variable {R : Type u} [Ring R] {M N : ModuleCat.{v} R} (f : M ⟶ N)

def normalMono (hf : Mono f) : NormalMono f where
  Z := of R (N ⧸ LinearMap.range f)
  g := f.range.mkQ
  w := LinearMap.range_mkQ_comp _
  isLimit :=
    /- The following [invalid Lean code](https://github.com/leanprover-community/lean/issues/341)
        might help you understand what's going on here:
        ```
        calc
        M   ≃ₗ[R] f.ker.quotient  : (Submodule.quotEquivOfEqBot _ (ker_eq_bot_of_mono _)).symm
        ... ≃ₗ[R] f.range         : LinearMap.quotKerEquivRange f
        ... ≃ₗ[R] r.range.mkQ.ker : LinearEquiv.ofEq _ _ (Submodule.ker_mkQ _).symm
        ```
      -/
        IsKernel.isoKernel _ _ (kernelIsLimit _)
          (LinearEquiv.toModuleIso'
            ((Submodule.quotEquivOfEqBot _ (ker_eq_bot_of_mono _)).symm ≪≫ₗ
              (LinearMap.quotKerEquivRange f ≪≫ₗ
              LinearEquiv.ofEq _ _ (Submodule.ker_mkQ _).symm))) <| by ext; rfl

def normalEpi (hf : Epi f) : NormalEpi f where
  W := of R (LinearMap.ker f)
  g := (LinearMap.ker f).subtype
  w := LinearMap.comp_ker_subtype _
  isColimit :=
    /- The following invalid Lean code might help you understand what's going on here:
        ```
        calc f.ker.subtype.range.quotient
            ≃ₗ[R] f.ker.quotient : Submodule.quotEquivOfEq _ _ (Submodule.range_subtype _)
        ... ≃ₗ[R] f.range        : LinearMap.quotKerEquivRange f
        ... ≃ₗ[R] N              : LinearEquiv.ofTop _ (range_eq_top_of_epi _)
        ```
      -/
        IsCokernel.cokernelIso _ _ (cokernelIsColimit _)
          (LinearEquiv.toModuleIso'
            (Submodule.quotEquivOfEq _ _ (Submodule.range_subtype _) ≪≫ₗ
                LinearMap.quotKerEquivRange f ≪≫ₗ
              LinearEquiv.ofTop _ (range_eq_top_of_epi _))) <| by ext; rfl

instance abelian : Abelian (ModuleCat.{v} R) where
  has_cokernels := hasCokernels_moduleCat
  normalMonoOfMono := normalMono
  normalEpiOfEpi := normalEpi

section ReflectsLimits

instance : HasLimitsOfSize.{v,v} (ModuleCatMax.{v, w} R) :=
  ModuleCat.hasLimitsOfSize.{v, v, max v w}

instance forget_reflectsLimitsOfSize :
    ReflectsLimitsOfSize.{v, v} (forget (ModuleCatMax.{v, w} R)) :=
  reflectsLimits_of_reflectsIsomorphisms

instance forget₂_reflectsLimitsOfSize :
    ReflectsLimitsOfSize.{v, v} (forget₂ (ModuleCatMax.{v, w} R) AddCommGrp.{max v w}) :=
  reflectsLimits_of_reflectsIsomorphisms

instance forget_reflectsLimits : ReflectsLimits (forget (ModuleCat.{v} R)) :=
  ModuleCat.forget_reflectsLimitsOfSize.{v, v}

instance forget₂_reflectsLimits : ReflectsLimits (forget₂ (ModuleCat.{v} R) AddCommGrp.{v}) :=
  ModuleCat.forget₂_reflectsLimitsOfSize.{v, v}

end ReflectsLimits

end ModuleCat
