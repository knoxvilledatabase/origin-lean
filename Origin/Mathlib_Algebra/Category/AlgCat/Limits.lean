/-
Extracted from Algebra/Category/AlgCat/Limits.lean
Genuine: 5 of 19 | Dissolved: 0 | Infrastructure: 14
-/
import Origin.Core

/-!
# The category of R-algebras has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.
-/

open CategoryTheory Limits

universe v w u t

noncomputable section

namespace AlgCat

variable {R : Type u} [CommRing R]

variable {J : Type v} [Category.{t} J] (F : J ⥤ AlgCat.{w} R)

-- INSTANCE (free from Core): semiringObj

-- INSTANCE (free from Core): algebraObj

def sectionsSubalgebra : Subalgebra R (∀ j, F.obj j) :=
  { SemiRingCat.sectionsSubsemiring
      (F ⋙ forget₂ (AlgCat R) RingCat.{w} ⋙ forget₂ RingCat SemiRingCat.{w}) with
    algebraMap_mem' := fun r _ _ f => (F.map f).hom.commutes r }

-- INSTANCE (free from Core): (F

-- INSTANCE (free from Core): (F

variable [Small.{w} (F ⋙ forget (AlgCat.{w} R)).sections]

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): limitSemiring

-- INSTANCE (free from Core): limitAlgebra

#adaptation_note /-- After nightly-2026-02-23 we need this to avoid timeouts. -/

set_option backward.isDefEq.respectTransparency false in

def limitπAlgHom (j) :
    (Types.Small.limitCone (F ⋙ forget (AlgCat R))).pt →ₐ[R]
      (F ⋙ forget (AlgCat.{w} R)).obj j :=
  letI : Small.{w}
      (Functor.sections ((F ⋙ forget₂ _ RingCat ⋙ forget₂ _ SemiRingCat) ⋙ forget _)) :=
    inferInstanceAs <| Small.{w} (F ⋙ forget _).sections
  { SemiRingCat.limitπRingHom
      (F ⋙ forget₂ (AlgCat R) RingCat.{w} ⋙ forget₂ RingCat SemiRingCat.{w}) j with
    toFun := (Types.Small.limitCone (F ⋙ forget (AlgCat.{w} R))).π.app j
    commutes' := fun x => by
      simp only [Functor.comp_obj, Types.Small.limitCone_pt, Functor.const_obj_obj,
        Types.Small.limitCone_π_app, ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk,
        ← Shrink.algEquiv_apply R, AlgEquiv.commutes]
      rfl
    }

namespace HasLimits

def limitCone : Cone F where
  pt := AlgCat.of R (Types.Small.limitCone (F ⋙ forget _)).pt
  π :=
    { app := fun j ↦ ofHom <| limitπAlgHom F j
      naturality := fun _ _ f => by
        ext
        simpa using (Types.Small.limitCone (F ⋙ forget _)).π.naturality_apply f _ }

set_option backward.isDefEq.respectTransparency false in

def limitConeIsLimit : IsLimit (limitCone.{v, w} F) := by
  refine
    IsLimit.ofFaithful (forget (AlgCat R)) (Types.Small.limitConeIsLimit.{v, w} _)
      (fun s => ofHom
        { toFun := _, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_,
          commutes' := ?_ })
      (fun s => rfl)
  · congr
    ext j
    simp
  · intro x y
    ext j
    simp
    rfl
  · ext j
    simp
    rfl
  · intro x y
    ext j
    simp
    rfl
  · intro r
    simp only [Equiv.algebraMap_def, Equiv.symm_symm]
    apply congrArg
    apply Subtype.ext
    ext j
    exact (s.π.app j).hom.commutes r

end HasLimits

open HasLimits

lemma hasLimitsOfSize [UnivLE.{v, w}] : HasLimitsOfSize.{t, v} (AlgCat.{w} R) :=
  { has_limits_of_shape := fun _ _ =>
    { has_limit := fun F => HasLimit.mk
        { cone := limitCone F
          isLimit := limitConeIsLimit F } } }

-- INSTANCE (free from Core): hasLimits

-- INSTANCE (free from Core): forget₂Ring_preservesLimitsOfSize

-- INSTANCE (free from Core): forget₂Ring_preservesLimits

-- INSTANCE (free from Core): forget₂Module_preservesLimitsOfSize

-- INSTANCE (free from Core): forget₂Module_preservesLimits

-- INSTANCE (free from Core): forget_preservesLimitsOfSize

-- INSTANCE (free from Core): forget_preservesLimits

end AlgCat
