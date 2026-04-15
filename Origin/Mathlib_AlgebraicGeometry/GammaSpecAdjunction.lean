/-
Extracted from AlgebraicGeometry/GammaSpecAdjunction.lean
Genuine: 12 of 12 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Adjunction between `Γ` and `Spec`

We define the adjunction `ΓSpec.adjunction : Γ ⊣ Spec` by defining the unit (`toΓSpec`,
in multiple steps in this file) and counit (done in `Spec.lean`) and checking that they satisfy
the left and right triangle identities. The constructions and proofs make use of
maps and lemmas defined and proved in `Mathlib/AlgebraicGeometry/StructureSheaf.lean`
extensively.

Notice that since the adjunction is between contravariant functors, you get to choose
one of the two categories to have arrows reversed, and it is equally valid to present
the adjunction as `Spec ⊣ Γ` (`Spec.to_LocallyRingedSpace.right_op ⊣ Γ`), in which
case the unit and the counit would switch to each other.

## Main definition

* `AlgebraicGeometry.identityToΓSpec` : The natural transformation `𝟭 _ ⟶ Γ ⋙ Spec`.
* `AlgebraicGeometry.ΓSpec.locallyRingedSpaceAdjunction` : The adjunction `Γ ⊣ Spec` from
  `CommRingᵒᵖ` to `LocallyRingedSpace`.
* `AlgebraicGeometry.ΓSpec.adjunction` : The adjunction `Γ ⊣ Spec` from
  `CommRingᵒᵖ` to `Scheme`.

-/

noncomputable section

universe u

open PrimeSpectrum

namespace AlgebraicGeometry

open Opposite

open CategoryTheory

open StructureSheaf

open Spec (structureSheaf)

open TopologicalSpace

open AlgebraicGeometry.LocallyRingedSpace

open TopCat.Presheaf

open TopCat.Presheaf.SheafCondition

namespace LocallyRingedSpace

variable (X : LocallyRingedSpace.{u})

def toΓSpecFun : X → PrimeSpectrum (Γ.obj (op X)) := fun x =>
  comap (X.presheaf.Γgerm x).hom (IsLocalRing.closedPoint (X.presheaf.stalk x))

set_option backward.isDefEq.respectTransparency false in

theorem notMem_prime_iff_unit_in_stalk (r : Γ.obj (op X)) (x : X) :
    r ∉ (X.toΓSpecFun x).asIdeal ↔ IsUnit (X.presheaf.Γgerm x r) := by
  simp [toΓSpecFun, IsLocalRing.closedPoint]

set_option backward.isDefEq.respectTransparency false in

theorem toΓSpec_preimage_basicOpen_eq (r : Γ.obj (op X)) :
    X.toΓSpecFun ⁻¹' basicOpen r = SetLike.coe (X.toRingedSpace.basicOpen r) := by
      ext
      dsimp
      simp only [Set.mem_preimage, SetLike.mem_coe]
      rw [X.toRingedSpace.mem_top_basicOpen]
      exact notMem_prime_iff_unit_in_stalk ..

theorem toΓSpec_continuous : Continuous X.toΓSpecFun := by
  rw [isTopologicalBasis_basic_opens.continuous_iff]
  rintro _ ⟨r, rfl⟩
  rw [X.toΓSpec_preimage_basicOpen_eq r]
  exact (X.toRingedSpace.basicOpen r).2

def toΓSpecBase : X.toTopCat ⟶ Spec.topObj (Γ.obj (op X)) :=
  TopCat.ofHom
  { toFun := X.toΓSpecFun
    continuous_toFun := X.toΓSpec_continuous }

variable (r : Γ.obj (op X))

abbrev toΓSpecMapBasicOpen : Opens X :=
  (Opens.map X.toΓSpecBase).obj (basicOpen r)

theorem toΓSpecMapBasicOpen_eq : X.toΓSpecMapBasicOpen r = X.toRingedSpace.basicOpen r :=
  Opens.ext (X.toΓSpec_preimage_basicOpen_eq r)

abbrev toToΓSpecMapBasicOpen :
    X.presheaf.obj (op ⊤) ⟶ X.presheaf.obj (op <| X.toΓSpecMapBasicOpen r) :=
  X.presheaf.map (X.toΓSpecMapBasicOpen r).leTop.op

set_option backward.isDefEq.respectTransparency false in

theorem isUnit_res_toΓSpecMapBasicOpen : IsUnit (X.toToΓSpecMapBasicOpen r r) := by
  convert
    (X.presheaf.map <| (eqToHom <| X.toΓSpecMapBasicOpen_eq r).op).hom.isUnit_map
      (X.toRingedSpace.isUnit_res_basicOpen r)
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  congr

def toΓSpecCApp :
    (structureSheaf <| Γ.obj <| op X).obj.obj (op <| basicOpen r) ⟶
      X.presheaf.obj (op <| X.toΓSpecMapBasicOpen r) :=
  -- note: the explicit type annotations were not needed before
  -- https://github.com/leanprover-community/mathlib4/pull/19757
  CommRingCat.ofHom <|
    IsLocalization.Away.lift
      (R := Γ.obj (op X))
      (S := (structureSheaf ↑(Γ.obj (op X))).obj.obj (op (basicOpen r)))
      r
      (isUnit_res_toΓSpecMapBasicOpen _ r)

set_option backward.isDefEq.respectTransparency false in

theorem toΓSpecCApp_iff
    (f :
      (structureSheaf <| Γ.obj <| op X).obj.obj (op <| basicOpen r) ⟶
        X.presheaf.obj (op <| X.toΓSpecMapBasicOpen r)) :
    CommRingCat.ofHom (algebraMap (Γ.obj (op X)) _) ≫ f = X.toToΓSpecMapBasicOpen r ↔
      f = X.toΓSpecCApp r := by
  have loc_inst := IsLocalization.to_basicOpen (Γ.obj (op X)) r
  refine ConcreteCategory.ext_iff.trans ?_
  rw [← @IsLocalization.Away.lift_comp _ _ _ _ _ _ _ r loc_inst _
      (X.isUnit_res_toΓSpecMapBasicOpen r)]
  constructor
  · intro h
    ext : 1
    exact IsLocalization.ringHom_ext (Submonoid.powers r) h
  apply congr_arg

theorem toΓSpecCApp_spec :
    CommRingCat.ofHom (algebraMap (Γ.obj (op X)) _) ≫ X.toΓSpecCApp r = X.toToΓSpecMapBasicOpen r :=
  (X.toΓSpecCApp_iff r _).2 rfl

set_option backward.isDefEq.respectTransparency false in
