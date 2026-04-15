/-
Extracted from CategoryTheory/Monoidal/Internal/Types/Basic.lean
Genuine: 9 of 12 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# `Mon Type u ≌ MonCat.{u}`

The category of internal monoid objects in `Type`
is equivalent to the category of "native" bundled monoids.

Moreover, this equivalence is compatible with the forgetful functors to `Type`.
-/

assert_not_exists MonoidWithZero

universe v u

open CategoryTheory MonObj ConcreteCategory

namespace MonTypeEquivalenceMon

-- INSTANCE (free from Core): monMonoid

noncomputable def functor : Mon (Type u) ⥤ MonCat.{u} where
  obj A := MonCat.of A.X
  map f := MonCat.ofHom
    { toFun := f.hom
      map_one' := congr_hom (IsMonHom.one_hom f.hom) PUnit.unit
      map_mul' x y := congr_hom (CC := fun X ↦ X) (IsMonHom.mul_hom f.hom) (x, y) }

attribute [local simp] types_tensorObj_def types_tensorUnit_def in

noncomputable def inverse : MonCat.{u} ⥤ Mon (Type u) where
  obj A :=
    { X := A
      mon :=
        { one := TypeCat.ofHom (fun _ => 1)
          mul := TypeCat.ofHom (fun p => p.1 * p.2)
          one_mul := by cat_disch
          mul_one := by cat_disch
          mul_assoc := by ext ⟨⟨x, y⟩, z⟩; simp [_root_.mul_assoc] } }
  map f := .mk' (TypeCat.ofHom f)
    (one_f := by
      #adaptation_note /-- Prior to https://github.com/leanprover/lean4/pull/12244
      this argument was provided by the auto_param. -/
      simp +instances only
      cat_disch)
    (mul_f := by
      #adaptation_note /-- Prior to https://github.com/leanprover/lean4/pull/12244
      this argument was provided by the auto_param. -/
      simp +instances only
      cat_disch)

end MonTypeEquivalenceMon

open MonTypeEquivalenceMon

noncomputable def monTypeEquivalenceMon : Mon (Type u) ≌ MonCat.{u} where
  functor := functor
  inverse := inverse
  unitIso := Iso.refl _
  counitIso := NatIso.ofComponents
    (fun A => MulEquiv.toMonCatIso { Equiv.refl _ with map_mul' := fun _ _ => rfl })
    (by cat_disch)

noncomputable def monTypeEquivalenceMonForget :
    MonTypeEquivalenceMon.functor ⋙ forget MonCat ≅ Mon.forget (Type u) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by cat_disch)

-- INSTANCE (free from Core): monTypeInhabited

namespace CommMonTypeEquivalenceCommMon

-- INSTANCE (free from Core): commMonCommMonoid

noncomputable def functor : CommMon (Type u) ⥤ CommMonCat.{u} where
  obj A := CommMonCat.of A.X
  map f := CommMonCat.ofHom (MonTypeEquivalenceMon.functor.map f.hom).hom

noncomputable def inverse : CommMonCat.{u} ⥤ CommMon (Type u) where
  obj A :=
    { MonTypeEquivalenceMon.inverse.obj ((forget₂ CommMonCat MonCat).obj A) with
      comm :=
        { mul_comm := by
            ext ⟨x : A, y : A⟩
            exact CommMonoid.mul_comm y x } }
  map f := CommMon.homMk (MonTypeEquivalenceMon.inverse.map ((forget₂ CommMonCat MonCat).map f))

end CommMonTypeEquivalenceCommMon

open CommMonTypeEquivalenceCommMon

noncomputable def commMonTypeEquivalenceCommMon : CommMon (Type u) ≌ CommMonCat.{u} where
  functor := functor
  inverse := inverse
  unitIso := Iso.refl _
  counitIso := NatIso.ofComponents
    (fun A => MulEquiv.toCommMonCatIso { Equiv.refl _ with map_mul' := fun _ _ => rfl })
    (by cat_disch)

noncomputable def commMonTypeEquivalenceCommMonForget :
    CommMonTypeEquivalenceCommMon.functor ⋙ forget₂ CommMonCat MonCat ≅
      CommMon.forget₂Mon (Type u) ⋙ MonTypeEquivalenceMon.functor :=
  Iso.refl _
