/-
Extracted from AlgebraicGeometry/Modules/Tilde.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Construction of M^~

Given any commutative ring `R` and `R`-module `M`, we construct the sheaf `M^~` of `𝒪_SpecR`-modules
such that `M^~(U)` is the set of dependent functions that are locally fractions.

## Main definitions
* `AlgebraicGeometry.tilde` : `M^~` as a sheaf of `𝒪_{Spec R}`-modules.
* `AlgebraicGeometry.tilde.adjunction` : `~` is left adjoint to taking global sections.

-/

universe u

open TopCat AlgebraicGeometry TopologicalSpace CategoryTheory Opposite

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R)

namespace AlgebraicGeometry

open _root_.PrimeSpectrum

def modulesSpecToSheaf :
    (Spec R).Modules ⥤ TopCat.Sheaf (ModuleCat R) (Spec R) :=
  SheafOfModules.forgetToSheafModuleCat (Spec R).ringCatSheaf (.op ⊤)
    (Limits.initialOpOfTerminal Limits.isTerminalTop) ⋙
  sheafCompose _ (ModuleCat.restrictScalars (StructureSheaf.globalSectionsIso R).hom.hom)

noncomputable

def moduleSpecΓFunctor : (Spec (.of R)).Modules ⥤ ModuleCat R :=
  modulesSpecToSheaf ⋙ TopCat.Sheaf.forget _ _ ⋙ (evaluation _ _).obj (.op ⊤)

set_option backward.isDefEq.respectTransparency false in

open PrimeSpectrum in

def SpecModulesToSheafFullyFaithful : (modulesSpecToSheaf (R := R)).FullyFaithful where
  preimage {M N} f := ⟨fun U ↦ ModuleCat.ofHom ⟨(f.1.app U).hom.toAddHom, by
    intro t m
    apply TopCat.Presheaf.IsSheaf.section_ext (modulesSpecToSheaf.obj N).2
    intro x hxU
    obtain ⟨a, ⟨_, ⟨r, rfl⟩, rfl⟩, hxr, hrU : basicOpen _ ≤ _⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxU U.unop.2
    refine ⟨_, hrU, hxr, ?_⟩
    refine Eq.trans ?_ (N.val.map_smul (homOfLE hrU).op t _).symm
    change N.1.map (homOfLE hrU).op (f.1.app _ _) = _ • N.1.map (homOfLE hrU).op (f.1.app _ _)
    have (x : _) :
        f.1.app _ (M.1.map (homOfLE hrU).op _) = N.1.map (homOfLE hrU).op (f.1.app _ x) :=
      congr($(f.1.naturality (homOfLE hrU).op).hom x)
    rw [← this, ← this, M.val.map_smul]
    generalize (Spec R).ringCatSheaf.obj.map (homOfLE hrU).op t = t
    letI := Module.compHom (R := Γ(Spec R, basicOpen r)) Γ(M, basicOpen r)
      (algebraMap R Γ(Spec R, basicOpen r))
    haveI : IsScalarTower R Γ(Spec R, basicOpen r) Γ(M, basicOpen r) :=
      .of_algebraMap_smul fun _ _ ↦ rfl
    letI := Module.compHom Γ(N, basicOpen r) (algebraMap R Γ(Spec R, basicOpen r))
    haveI : IsScalarTower R Γ(Spec R, basicOpen r) Γ(N, basicOpen r) :=
      .of_algebraMap_smul fun _ _ ↦ rfl
    exact (IsLocalization.linearMap_compatibleSMul (.powers (M := R) r)
      Γ(Spec R, basicOpen r) Γ(M, basicOpen r) Γ(N, basicOpen r)).map_smul
      (f.hom.app _).hom _ _⟩, fun i ↦ by ext x; exact congr($(f.1.naturality i).hom x)⟩
  map_preimage f := rfl
  preimage_map f := rfl

def tilde : (Spec R).Modules where
  val := moduleStructurePresheaf R M
  isSheaf := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat) _).2
    (structureSheafInType R M).2

namespace tilde

set_option backward.isDefEq.respectTransparency false in

noncomputable

def modulesSpecToSheafIso :
    (modulesSpecToSheaf.obj (tilde M)).1 ≅ structurePresheafInModuleCat R M :=
  NatIso.ofComponents (fun U ↦ LinearEquiv.toModuleIso
    (X₁ := (modulesSpecToSheaf.obj (tilde M)).presheaf.obj _)
    { __ := AddEquiv.refl _,
      map_smul' r m := IsScalarTower.algebraMap_smul (M := ((structureSheafInType R M).obj.obj U))
        ((structureSheafInType R R).obj.obj U) r m }) fun _ ↦ rfl

def toOpen (U : (Spec R).Opens) : M ⟶ (modulesSpecToSheaf.obj (tilde M)).presheaf.obj (.op U) :=
  ModuleCat.ofHom (StructureSheaf.toOpenₗ R M U) ≫ ((modulesSpecToSheafIso M).app _).inv
