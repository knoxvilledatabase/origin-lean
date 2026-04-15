/-
Extracted from Algebra/Category/Ring/FilteredColimits.lean
Genuine: 22 of 37 | Dissolved: 0 | Infrastructure: 15
-/
import Origin.Core

/-!
# The forgetful functor from (commutative) (semi-) rings preserves filtered colimits.

Forgetful functors from algebraic categories usually don't preserve colimits. However, they tend
to preserve _filtered_ colimits.

In this file, we start with a small filtered category `J` and a functor `F : J ⥤ SemiRingCat`.
We show that the colimit of `F ⋙ forget₂ SemiRingCat MonCat` (in `MonCat`)
carries the structure of a semiring, thereby showing that the forgetful functor
`forget₂ SemiRingCat MonCat` preserves filtered colimits.
In particular, this implies that `forget SemiRingCat` preserves filtered colimits.
Similarly for `CommSemiRingCat`, `RingCat` and `CommRingCat`.

-/

universe v u

noncomputable section

open CategoryTheory Limits

open IsFiltered renaming max → max' -- avoid name collision with `_root_.max`.

open AddMonCat.FilteredColimits (colimit_zero_eq colimit_add_mk_eq)

open MonCat.FilteredColimits (colimit_one_eq colimit_mul_mk_eq)

namespace SemiRingCat.FilteredColimits

variable {J : Type v} [SmallCategory J] (F : J ⥤ SemiRingCat.{max v u})

-- INSTANCE (free from Core): semiringObj

variable [IsFiltered J]

abbrev R : MonCat.{max v u} :=
  MonCat.FilteredColimits.colimit.{v, u} (F ⋙ forget₂ SemiRingCat.{max v u} MonCat)

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): colimitSemiring

def colimit : SemiRingCat.{max v u} :=
  SemiRingCat.of <| R.{v, u} F

def colimitCocone : Cocone F where
  pt := colimit.{v, u} F
  ι :=
    { app := fun j => ofHom
        { ((MonCat.FilteredColimits.colimitCocone
            (F ⋙ forget₂ SemiRingCat.{max v u} MonCat)).ι.app j).hom,
            ((AddCommMonCat.FilteredColimits.colimitCocone
              (F ⋙ forget₂ SemiRingCat.{max v u} AddCommMonCat)).ι.app j).hom with }
      naturality _ _ f := by
        ext
        simpa using (Types.TypeMax.colimitCocone (F ⋙ forget SemiRingCat)).ι.naturality_apply f _ }

namespace colimitCoconeIsColimit

variable {F} (t : Cocone F)

def descAddMonoidHom : R F →+ t.1 :=
  ((AddCommMonCat.FilteredColimits.colimitCoconeIsColimit.{v, u}
    (F ⋙ forget₂ SemiRingCat AddCommMonCat)).desc
      ((forget₂ SemiRingCat AddCommMonCat).mapCocone t)).hom

lemma descAddMonoidHom_quotMk {j : J} (x : F.obj j) :
    descAddMonoidHom t (Quot.mk _ ⟨j, x⟩) = t.ι.app j x :=
  ConcreteCategory.congr_hom ((forget AddCommMonCat).congr_map
    ((AddCommMonCat.FilteredColimits.colimitCoconeIsColimit.{v, u}
      (F ⋙ forget₂ SemiRingCat AddCommMonCat)).fac
        ((forget₂ SemiRingCat AddCommMonCat).mapCocone t) j)) x

def descMonoidHom : R F →* t.1 :=
  ((MonCat.FilteredColimits.colimitCoconeIsColimit.{v, u}
    (F ⋙ forget₂ _ _)).desc ((forget₂ _ _).mapCocone t)).hom

lemma descMonoidHom_quotMk {j : J} (x : F.obj j) :
    descMonoidHom t (Quot.mk _ ⟨j, x⟩) = t.ι.app j x :=
  ConcreteCategory.congr_hom ((forget MonCat).congr_map
    ((MonCat.FilteredColimits.colimitCoconeIsColimit.{v, u}
      (F ⋙ forget₂ _ _)).fac ((forget₂ _ _).mapCocone t) j)) x

lemma descMonoidHom_apply_eq (x : R F) :
    descMonoidHom t x = descAddMonoidHom t x := by
  obtain ⟨j, x⟩ := x
  rw [descMonoidHom_quotMk t x, descAddMonoidHom_quotMk t x]

end colimitCoconeIsColimit

open colimitCoconeIsColimit in

def colimitCoconeIsColimit : IsColimit <| colimitCocone.{v, u} F where
  desc t := ofHom
    { descAddMonoidHom t with
      map_one' := (descMonoidHom_apply_eq t 1).symm.trans (by simp)
      map_mul' x y := by
        change descAddMonoidHom t (x * y) =
          descAddMonoidHom t x * descAddMonoidHom t y
        simp [← descMonoidHom_apply_eq] }
  fac t j := by ext x; exact descAddMonoidHom_quotMk t x
  uniq t m hm := by
    ext ⟨j, x⟩
    exact (ConcreteCategory.congr_hom ((forget SemiRingCat).congr_map (hm j)) x).trans
      (descAddMonoidHom_quotMk t x).symm

-- INSTANCE (free from Core): forget₂Mon_preservesFilteredColimits

-- INSTANCE (free from Core): forget_preservesFilteredColimits

end

end SemiRingCat.FilteredColimits

namespace CommSemiRingCat.FilteredColimits

variable {J : Type v} [SmallCategory J] [IsFiltered J] (F : J ⥤ CommSemiRingCat.{max v u})

abbrev R : SemiRingCat.{max v u} :=
  SemiRingCat.FilteredColimits.colimit (F ⋙ forget₂ CommSemiRingCat SemiRingCat.{max v u})

-- INSTANCE (free from Core): colimitCommSemiring

def colimit : CommSemiRingCat.{max v u} :=
  CommSemiRingCat.of <| R.{v, u} F

def colimitCocone : Cocone F where
  pt := colimit.{v, u} F
  ι :=
    { app := fun X ↦ ofHom <| ((SemiRingCat.FilteredColimits.colimitCocone
          (F ⋙ forget₂ CommSemiRingCat SemiRingCat.{max v u})).ι.app X).hom
      naturality _ _ f := by
        ext
        simpa using (Types.TypeMax.colimitCocone
          (F ⋙ forget CommSemiRingCat)).ι.naturality_apply f _ }

def colimitCoconeIsColimit : IsColimit <| colimitCocone.{v, u} F :=
  isColimitOfReflects (forget₂ _ SemiRingCat)
    (SemiRingCat.FilteredColimits.colimitCoconeIsColimit
      (F ⋙ forget₂ CommSemiRingCat SemiRingCat))

-- INSTANCE (free from Core): forget₂SemiRing_preservesFilteredColimits

-- INSTANCE (free from Core): forget_preservesFilteredColimits

end

end CommSemiRingCat.FilteredColimits

namespace RingCat.FilteredColimits

variable {J : Type v} [SmallCategory J] [IsFiltered J] (F : J ⥤ RingCat.{max v u})

abbrev R : SemiRingCat.{max v u} :=
  SemiRingCat.FilteredColimits.colimit.{v, u} (F ⋙ forget₂ RingCat SemiRingCat.{max v u})

-- INSTANCE (free from Core): colimitRing

def colimit : RingCat.{max v u} :=
  RingCat.of <| R.{v, u} F

def colimitCocone : Cocone F where
  pt := colimit.{v, u} F
  ι :=
    { app := fun X ↦ ofHom <| ((SemiRingCat.FilteredColimits.colimitCocone
          (F ⋙ forget₂ RingCat SemiRingCat.{max v u})).ι.app X).hom
      naturality _ _ f := by
        ext
        simpa using (Types.TypeMax.colimitCocone (F ⋙ forget RingCat)).ι.naturality_apply f _ }

def colimitCoconeIsColimit : IsColimit <| colimitCocone.{v, u} F :=
  isColimitOfReflects (forget₂ _ _)
    (SemiRingCat.FilteredColimits.colimitCoconeIsColimit
      (F ⋙ forget₂ RingCat SemiRingCat))

-- INSTANCE (free from Core): forget₂SemiRing_preservesFilteredColimits

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): forget_preservesFilteredColimits

end

end RingCat.FilteredColimits

namespace CommRingCat.FilteredColimits

variable {J : Type v} [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{max v u})

abbrev R : RingCat.{max v u} :=
  RingCat.FilteredColimits.colimit.{v, u} (F ⋙ forget₂ CommRingCat RingCat.{max v u})

-- INSTANCE (free from Core): colimitCommRing

def colimit : CommRingCat.{max v u} :=
  CommRingCat.of <| R.{v, u} F

def colimitCocone : Cocone F where
  pt := colimit.{v, u} F
  ι :=
    { app := fun X ↦ ofHom <| ((RingCat.FilteredColimits.colimitCocone
          (F ⋙ forget₂ CommRingCat RingCat.{max v u})).ι.app X).hom
      naturality _ _ f := by
        ext
        simpa using (Types.TypeMax.colimitCocone (F ⋙ forget CommRingCat)).ι.naturality_apply f _ }

def colimitCoconeIsColimit : IsColimit <| colimitCocone.{v, u} F :=
  isColimitOfReflects (forget₂ _ _)
    (RingCat.FilteredColimits.colimitCoconeIsColimit
      (F ⋙ forget₂ CommRingCat RingCat))

-- INSTANCE (free from Core): forget₂Ring_preservesFilteredColimits

-- INSTANCE (free from Core): forget_preservesFilteredColimits

omit [IsFiltered J] in

protected lemma nontrivial {F : J ⥤ CommRingCat.{v}} [IsFilteredOrEmpty J]
    [∀ i, Nontrivial (F.obj i)] {c : Cocone F} (hc : IsColimit c) : Nontrivial c.pt := by
  classical
  cases isEmpty_or_nonempty J
  · exact ((isColimitEquivIsInitialOfIsEmpty _ _ hc).to (.of (ULift ℤ))).hom.domain_nontrivial
  have i := ‹Nonempty J›.some
  refine ⟨c.ι.app i 0, c.ι.app i 1, fun h ↦ ?_⟩
  have : IsFiltered J := ⟨⟩
  obtain ⟨k, f, e⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff' (isColimitOfPreserves (forget _) hc) _ _).mp h
  exact zero_ne_one (((F.map f).hom.map_zero.symm.trans e).trans (F.map f).hom.map_one)

omit [IsFiltered J] in

-- INSTANCE (free from Core): {F

end

end CommRingCat.FilteredColimits
