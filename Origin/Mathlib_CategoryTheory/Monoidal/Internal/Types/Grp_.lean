/-
Extracted from CategoryTheory/Monoidal/Internal/Types/Grp_.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# `Grp (Type u) ≌ GrpCat.{u}`

The category of internal group objects in `Type`
is equivalent to the category of "native" bundled groups.

Moreover, this equivalence is compatible with the forgetful functors to `Type`.
-/

assert_not_exists Field

universe v u

open CategoryTheory MonObj

namespace GrpTypeEquivalenceGrp

-- INSTANCE (free from Core): grpGroup

noncomputable def functor : Grp (Type u) ⥤ GrpCat.{u} where
  obj A := GrpCat.of A.X
  map f := GrpCat.ofHom (MonTypeEquivalenceMon.functor.map f.hom).hom

noncomputable def inverse : GrpCat.{u} ⥤ Grp (Type u) where
  obj A :=
    { MonTypeEquivalenceMon.inverse.obj ((forget₂ GrpCat MonCat).obj A) with
      grp :=
        { inv := TypeCat.ofHom ((·⁻¹) : A → A)
          left_inv := by
            ext x
            exact inv_mul_cancel (G := A) x
          right_inv := by
            ext x
            exact mul_inv_cancel (G := A) x } }
  map f := Grp.homMk' (MonTypeEquivalenceMon.inverse.map ((forget₂ GrpCat MonCat).map f))

end GrpTypeEquivalenceGrp

noncomputable def grpTypeEquivalenceGrp : Grp (Type u) ≌ GrpCat.{u} where
  functor := GrpTypeEquivalenceGrp.functor
  inverse := GrpTypeEquivalenceGrp.inverse
  unitIso := Iso.refl _
  counitIso := NatIso.ofComponents
    (fun A => MulEquiv.toGrpIso { Equiv.refl _ with map_mul' := fun _ _ => rfl })
    (by cat_disch)

noncomputable def grpTypeEquivalenceGrpForget :
    GrpTypeEquivalenceGrp.functor ⋙ forget₂ GrpCat MonCat ≅
      Grp.forget₂Mon (Type u) ⋙ MonTypeEquivalenceMon.functor :=
  Iso.refl _
