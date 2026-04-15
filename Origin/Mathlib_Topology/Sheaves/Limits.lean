/-
Extracted from Topology/Sheaves/Limits.lean
Genuine: 2 of 10 | Dissolved: 0 | Infrastructure: 8
-/
import Origin.Core

/-!
# Presheaves in `C` have limits and colimits when `C` does.
-/

noncomputable section

universe v u w t

open CategoryTheory

open CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {J : Type w} [Category* J]

namespace TopCat

-- INSTANCE (free from Core): [HasLimitsOfShape

-- INSTANCE (free from Core): [HasLimits

-- INSTANCE (free from Core): [HasColimitsOfShape

-- INSTANCE (free from Core): [HasColimits.{v,

-- INSTANCE (free from Core): [HasLimitsOfShape

-- INSTANCE (free from Core): [HasLimitsOfShape

-- INSTANCE (free from Core): [HasLimits

-- INSTANCE (free from Core): [HasLimits

set_option backward.isDefEq.respectTransparency false in

theorem isSheaf_of_isLimit [HasLimitsOfShape J C] {X : TopCat} (F : J ⥤ Presheaf.{v} C X)
    (H : ∀ j, (F.obj j).IsSheaf) {c : Cone F} (hc : IsLimit c) : c.pt.IsSheaf := by
  let F' : J ⥤ Sheaf C X :=
    { obj := fun j => ⟨F.obj j, H j⟩
      map := fun f => ⟨F.map f⟩ }
  let e : F' ⋙ Sheaf.forget C X ≅ F := NatIso.ofComponents fun _ => Iso.refl _
  exact Presheaf.isSheaf_of_iso
    ((isLimitOfPreserves (Sheaf.forget C X) (limit.isLimit F')).conePointsIsoOfNatIso hc e)
    (limit F').2

theorem limit_isSheaf [HasLimitsOfShape J C] {X : TopCat} (F : J ⥤ Presheaf.{v} C X)
    (H : ∀ j, (F.obj j).IsSheaf) : (limit F).IsSheaf :=
  isSheaf_of_isLimit F H (limit.isLimit F)

end TopCat
