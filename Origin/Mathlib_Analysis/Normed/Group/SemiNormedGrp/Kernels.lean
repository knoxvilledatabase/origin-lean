/-
Extracted from Analysis/Normed/Group/SemiNormedGrp/Kernels.lean
Genuine: 10 of 16 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core

/-!
# Kernels and cokernels in SemiNormedGrp₁ and SemiNormedGrp

We show that `SemiNormedGrp₁` has cokernels
(for which of course the `cokernel.π f` maps are norm non-increasing),
as well as the easier result that `SemiNormedGrp` has cokernels. We also show that
`SemiNormedGrp` has kernels.

So far, I don't see a way to state nicely what we really want:
`SemiNormedGrp` has cokernels, and `cokernel.π f` is norm non-increasing.
The problem is that the limits API doesn't promise you any particular model of the cokernel,
and in `SemiNormedGrp` one can always take a cokernel and rescale its norm
(and hence making `cokernel.π f` arbitrarily large in norm), obtaining another categorical cokernel.

-/

open CategoryTheory CategoryTheory.Limits

universe u

namespace SemiNormedGrp₁

noncomputable section

def cokernelCocone {X Y : SemiNormedGrp₁.{u}} (f : X ⟶ Y) : Cofork f 0 :=
  Cofork.ofπ
    (@SemiNormedGrp₁.mkHom _ (Y ⧸ NormedAddGroupHom.range f.1) _ _
      f.hom.1.range.normedMk (NormedAddGroupHom.isQuotientQuotient _).norm_le)
    (by
      ext x
      rw [Limits.zero_comp, comp_apply, SemiNormedGrp₁.mkHom_apply,
        SemiNormedGrp₁.zero_apply, ← NormedAddGroupHom.mem_ker, f.hom.1.range.ker_normedMk,
        f.hom.1.mem_range]
      use x)

def cokernelLift {X Y : SemiNormedGrp₁.{u}} (f : X ⟶ Y) (s : CokernelCofork f) :
    (cokernelCocone f).pt ⟶ s.pt := by
  fconstructor
  -- The lift itself:
  · apply NormedAddGroupHom.lift _ s.π.1
    rintro _ ⟨b, rfl⟩
    change (f ≫ s.π) b = 0
    simp
  -- The lift has norm at most one:
  exact NormedAddGroupHom.lift_normNoninc _ _ _ s.π.2

-- INSTANCE (free from Core): :

example : HasCokernels SemiNormedGrp₁ := by infer_instance

end

end SemiNormedGrp₁

namespace SemiNormedGrp

section EqualizersAndKernels

-- INSTANCE (free from Core): {V

-- INSTANCE (free from Core): {V

noncomputable def fork {V W : SemiNormedGrp.{u}} (f g : V ⟶ W) : Fork f g :=
  @Fork.ofι _ _ _ _ _ _ (of (f - g).hom.ker)
    (ofHom (NormedAddGroupHom.incl (f - g).hom.ker)) <| by
    ext v
    have : v.1 ∈ (f - g).hom.ker := v.2
    simpa [-SetLike.coe_mem, NormedAddGroupHom.mem_ker, sub_eq_zero] using this

-- INSTANCE (free from Core): hasLimit_parallelPair

-- INSTANCE (free from Core): :

end EqualizersAndKernels

section Cokernel

noncomputable

def cokernelCocone {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y) : Cofork f 0 :=
  Cofork.ofπ (P := SemiNormedGrp.of (Y ⧸ NormedAddGroupHom.range f.hom))
    (ofHom f.hom.range.normedMk)
    (by aesop)

noncomputable

def cokernelLift {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y) (s : CokernelCofork f) :
    (cokernelCocone f).pt ⟶ s.pt :=
  ofHom <| NormedAddGroupHom.lift _ s.π.hom
    (by
      rintro _ ⟨b, rfl⟩
      change (f ≫ s.π) b = 0
      simp)

noncomputable

def isColimitCokernelCocone {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y) :
    IsColimit (cokernelCocone f) :=
  isColimitAux _ (cokernelLift f)
    (fun s => by
      ext
      apply NormedAddGroupHom.lift_mk f.hom.range
      rintro _ ⟨b, rfl⟩
      change (f ≫ s.π) b = 0
      simp)
    fun _ _ w => SemiNormedGrp.hom_ext <| NormedAddGroupHom.lift_unique f.hom.range _ _ _ <|
      congr_arg Hom.hom w

-- INSTANCE (free from Core): :

example : HasCokernels SemiNormedGrp := by infer_instance

section ExplicitCokernel

noncomputable

def explicitCokernel {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y) : SemiNormedGrp.{u} :=
  (cokernelCocone f).pt

noncomputable

def explicitCokernelDesc {X Y Z : SemiNormedGrp.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} (w : f ≫ g = 0) :
    explicitCokernel f ⟶ Z :=
  (isColimitCokernelCocone f).desc (Cofork.ofπ g (by simp [w]))

noncomputable

def explicitCokernelπ {X Y : SemiNormedGrp.{u}} (f : X ⟶ Y) : Y ⟶ explicitCokernel f :=
  (cokernelCocone f).ι.app WalkingParallelPair.one

theorem explicitCokernelπ_surjective {X Y : SemiNormedGrp.{u}} {f : X ⟶ Y} :
    Function.Surjective (explicitCokernelπ f) :=
  Quot.mk_surjective

set_option backward.isDefEq.respectTransparency false in
