/-
Extracted from Algebra/Category/ModuleCat/Kernels.lean
Genuine: 9 of 9 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The concrete (co)kernels in the category of modules are (co)kernels in the categorical sense.
-/

open CategoryTheory CategoryTheory.Limits

universe u v

namespace ModuleCat

variable {R : Type u} [Ring R]

variable {M N P : ModuleCat.{v} R} (f : M ⟶ N)

def kernelCone : KernelFork f :=
  KernelFork.ofι (ofHom (LinearMap.ker f.hom).subtype) <| by aesop

def kernelIsLimit : IsLimit (kernelCone f) :=
  Fork.IsLimit.mk _
    (fun s => ofHom <|
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11036): broken dot notation on LinearMap.ker
      LinearMap.codRestrict (LinearMap.ker f.hom) (Fork.ι s).hom fun c =>
        LinearMap.mem_ker.2 <| by simp [← ConcreteCategory.comp_apply])
    (fun _ => hom_ext <| LinearMap.subtype_comp_codRestrict _ _ _) fun s m h =>
      hom_ext <| LinearMap.ext fun x => Subtype.ext_iff.2 (by simp [← h]; rfl)

set_option backward.isDefEq.respectTransparency false in

noncomputable

def isLimitKernelFork (f : M ⟶ N) (g : N ⟶ P) (H : Function.Exact f.hom g.hom)
    (H₂ : Function.Injective f.hom) :
    IsLimit (KernelFork.ofι (f := g) f (by ext; exact H.apply_apply_eq_zero _)) := by
  refine IsLimit.ofIsoLimit (kernelIsLimit g) <|
    Cone.ext ((LinearEquiv.ofInjective _ H₂).trans
        (LinearEquiv.ofEq _ _ (LinearMap.exact_iff.mp H).symm)).toModuleIso.symm ?_
  · rintro ⟨⟩ <;> ext x <;> simp [kernelCone]

def cokernelCocone : CokernelCofork f :=
  CokernelCofork.ofπ (ofHom (LinearMap.range f.hom).mkQ) <| hom_ext <| LinearMap.range_mkQ_comp _

def cokernelIsColimit : IsColimit (cokernelCocone f) :=
  Cofork.IsColimit.mk _
    (fun s => ofHom <| (LinearMap.range f.hom).liftQ (Cofork.π s).hom <|
      LinearMap.range_le_ker_iff.2 <| ModuleCat.hom_ext_iff.mp <| CokernelCofork.condition s)
    (fun s => hom_ext <| (LinearMap.range f.hom).liftQ_mkQ (Cofork.π s).hom _) fun s m h => by
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11036): broken dot notation
    haveI : Epi (ofHom (LinearMap.range f.hom).mkQ) :=
      (epi_iff_range_eq_top _).mpr (Submodule.range_mkQ _)
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11036): broken dot notation
    apply (cancel_epi (ofHom (LinearMap.range f.hom).mkQ)).1
    exact h

noncomputable

def isColimitCokernelCofork (f : M ⟶ N) (g : N ⟶ P) (H : Function.Exact f.hom g.hom)
    (H₂ : Function.Surjective g.hom) :
    IsColimit (CokernelCofork.ofπ (f := f) g (by ext; exact H.apply_apply_eq_zero _)) := by
  refine IsColimit.ofIsoColimit (ModuleCat.cokernelIsColimit f) <|
    Cocone.ext (((Submodule.quotEquivOfEq _ _ (LinearMap.exact_iff.mp H)).toModuleIso).symm
    ≪≫ ((LinearMap.quotKerEquivOfSurjective _ H₂).toModuleIso)) ?_
  · rintro ⟨⟩ <;> ext x
    · simpa using (Function.Exact.apply_apply_eq_zero H x).symm
    · rfl

end

theorem hasKernels_moduleCat : HasKernels (ModuleCat R) :=
  ⟨fun f => HasLimit.mk ⟨_, kernelIsLimit f⟩⟩

theorem hasCokernels_moduleCat : HasCokernels (ModuleCat R) :=
  ⟨fun f => HasColimit.mk ⟨_, cokernelIsColimit f⟩⟩

open ModuleCat

attribute [local instance] hasKernels_moduleCat

attribute [local instance] hasCokernels_moduleCat

variable {G H : ModuleCat.{v} R} (f : G ⟶ H)

noncomputable def kernelIsoKer {G H : ModuleCat.{v} R} (f : G ⟶ H) :
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11036): broken dot notation
    kernel f ≅ ModuleCat.of R (LinearMap.ker f.hom) :=
  limit.isoLimitCone ⟨_, kernelIsLimit f⟩
