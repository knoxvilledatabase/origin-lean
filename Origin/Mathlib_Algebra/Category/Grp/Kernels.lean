/-
Extracted from Algebra/Category/Grp/Kernels.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The concrete (co)kernels in the category of abelian groups are categorical (co)kernels.
-/

namespace AddCommGrpCat

open AddMonoidHom CategoryTheory Limits QuotientAddGroup

universe u

variable {G H : AddCommGrpCat.{u}} (f : G ⟶ H)

def kernelCone : KernelFork f :=
  KernelFork.ofι (Z := of f.hom.ker) (ofHom f.hom.ker.subtype) <| ext fun x =>
    x.casesOn fun _ hx => hx

def kernelIsLimit : IsLimit <| kernelCone f :=
  Fork.IsLimit.mk _
    (fun s => ofHom <| s.ι.hom.codRestrict _ fun c => mem_ker.mpr <|
      ConcreteCategory.congr_hom s.condition c)
    (fun _ => by rfl)
    (fun _ _ h => ext fun x => Subtype.ext_iff.mpr <| ConcreteCategory.congr_hom h x)

def cokernelCocone : CokernelCofork f :=
  CokernelCofork.ofπ (Z := of <| H ⧸ f.hom.range) (ofHom (mk' f.hom.range)) <| ext fun x =>
    (eq_zero_iff _).mpr ⟨x, rfl⟩

def cokernelIsColimit : IsColimit <| cokernelCocone f :=
  Cofork.IsColimit.mk _
    (fun s => ofHom <| lift _ _ <| (range_le_ker_iff _ _).mpr <|
      congr_arg Hom.hom (CokernelCofork.condition s))
    (fun _ => rfl)
    (fun _ _ h => have : Epi (cokernelCocone f).π := (epi_iff_surjective _).mpr <| mk'_surjective _
      (cancel_epi (cokernelCocone f).π).mp <| by simpa only [parallelPair_obj_one] using h)

end AddCommGrpCat
