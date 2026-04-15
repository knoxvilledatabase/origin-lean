/-
Extracted from Geometry/RingedSpace/LocallyRingedSpace/HasColimits.lean
Genuine: 5 of 8 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Colimits of LocallyRingedSpace

We construct the explicit coproducts and coequalizers of `LocallyRingedSpace`.
It then follows that `LocallyRingedSpace` has all colimits, and
`forgetToSheafedSpace` preserves them.

-/

namespace AlgebraicGeometry

universe w' w v u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

attribute [local instance] Opposite.small

namespace SheafedSpace

variable {C : Type u} [Category.{v} C]

variable {J : Type w} [Category.{w'} J] [Small.{v} J] (F : J ⥤ SheafedSpace.{_, _, v} C)

theorem isColimit_exists_rep [HasLimitsOfShape Jᵒᵖ C] {c : Cocone F} (hc : IsColimit c) (x : c.pt) :
    ∃ (i : J) (y : F.obj i), (c.ι.app i).hom.base y = x :=
  Concrete.isColimit_exists_rep (F ⋙ forget C) (isColimitOfPreserves (forget C) hc) x

theorem colimit_exists_rep [HasLimitsOfShape Jᵒᵖ C] (x : colimit (C := SheafedSpace C) F) :
    ∃ (i : J) (y : F.obj i), (colimit.ι F i).hom.base y = x :=
  Concrete.isColimit_exists_rep (F ⋙ SheafedSpace.forget C)
    (isColimitOfPreserves (SheafedSpace.forget _) (colimit.isColimit F)) x

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): [HasLimits

end SheafedSpace

namespace LocallyRingedSpace

section HasCoproducts

variable {ι : Type v} [Small.{u} ι] (F : Discrete ι ⥤ LocallyRingedSpace.{u})

noncomputable def coproduct : LocallyRingedSpace where
  toSheafedSpace := colimit (C := SheafedSpace.{u + 1, u, u} CommRingCat.{u})
    (F ⋙ forgetToSheafedSpace)
  isLocalRing x := by
    obtain ⟨i, y, ⟨⟩⟩ := SheafedSpace.colimit_exists_rep (F ⋙ forgetToSheafedSpace) x
    haveI : IsLocalRing (((F ⋙ forgetToSheafedSpace).obj i).presheaf.stalk y) :=
      (F.obj i).isLocalRing _
    exact
      (asIso ((colimit.ι (C := SheafedSpace.{u + 1, u, u} CommRingCat.{u})
        (F ⋙ forgetToSheafedSpace) i :).hom.stalkMap y)).symm.commRingCatIsoToRingEquiv.isLocalRing

set_option backward.isDefEq.respectTransparency false in

noncomputable def coproductCofan : Cocone F where
  pt := coproduct F
  ι :=
    { app j := LocallyRingedSpace.homMk (colimit.ι (F ⋙ forgetToSheafedSpace) j)
      naturality := fun ⟨j⟩ ⟨j'⟩ ⟨⟨(f : j = j')⟩⟩ => by subst f; simp }

set_option backward.isDefEq.respectTransparency false in

noncomputable def coproductCofanIsColimit : IsColimit (coproductCofan F) where
  desc s :=
    LocallyRingedSpace.homMk (colimit.desc
      (F ⋙ forgetToSheafedSpace) (forgetToSheafedSpace.mapCocone s)) (by
        intro x
        obtain ⟨i, y, ⟨⟩⟩ := SheafedSpace.colimit_exists_rep (F ⋙ forgetToSheafedSpace) x
        have := PresheafedSpace.stalkMap.comp
          (colimit.ι (F ⋙ forgetToSheafedSpace) i).hom
          (colimit.desc (F ⋙ forgetToSheafedSpace) (forgetToSheafedSpace.mapCocone s)).hom y
        simp only [← IsIso.comp_inv_eq,
          ← InducedCategory.comp_hom,
          PresheafedSpace.stalkMap.congr_hom _ _
            (congr_arg (InducedCategory.Hom.hom) (colimit.ι_desc
              (forgetToSheafedSpace.mapCocone s) i))] at this
        rw [← this]
        dsimp
        infer_instance)
  fac _ _ :=
    LocallyRingedSpace.forgetToSheafedSpace.map_injective
     (colimit.ι_desc (C := SheafedSpace _) _ _)
  uniq s f h :=
    LocallyRingedSpace.forgetToSheafedSpace.map_injective
      (IsColimit.uniq _ (forgetToSheafedSpace.mapCocone s) f.toShHom fun j =>
        congr_arg LocallyRingedSpace.Hom.toShHom (h j))

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

end HasCoproducts

section HasCoequalizer

variable {X Y : LocallyRingedSpace.{v}} (f g : X ⟶ Y)

namespace HasCoequalizer

set_option backward.isDefEq.respectTransparency false in
