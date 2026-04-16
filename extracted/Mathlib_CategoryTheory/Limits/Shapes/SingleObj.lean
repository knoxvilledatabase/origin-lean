/-
Extracted from CategoryTheory/Limits/Shapes/SingleObj.lean
Genuine: 5 | Conflates: 0 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Data.Setoid.Basic
import Mathlib.GroupTheory.GroupAction.Defs

noncomputable section

/-!
# (Co)limits of functors out of `SingleObj M`

We characterise (co)limits of shape `SingleObj M`. Currently only in the category of types.

## Main results

* `SingleObj.Types.limitEquivFixedPoints`: The limit of `J : SingleObj G ⥤ Type u` is the fixed
  points of `J.obj (SingleObj.star G)` under the induced action.

* `SingleObj.Types.colimitEquivQuotient`: The colimit of `J : SingleObj G ⥤ Type u` is the
  quotient of `J.obj (SingleObj.star G)` by the induced action.

-/

universe u v

namespace CategoryTheory

namespace Limits

namespace SingleObj

variable {M G : Type v} [Monoid M] [Group G]

instance (J : SingleObj M ⥤ Type u) : MulAction M (J.obj (SingleObj.star M)) where
  smul g x := J.map g x
  one_smul x := by
    show J.map (𝟙 _) x = x
    simp only [FunctorToTypes.map_id_apply]
  mul_smul g h x := by
    show J.map (g * h) x = (J.map h ≫ J.map g) x
    rw [← SingleObj.comp_as_mul]
    · simp only [FunctorToTypes.map_comp_apply, types_comp_apply]
      rfl

section Limits

variable (J : SingleObj M ⥤ Type u)

@[simps]
def Types.sections.equivFixedPoints :
    J.sections ≃ MulAction.fixedPoints M (J.obj (SingleObj.star M)) where
  toFun s := ⟨s.val _, s.property⟩
  invFun p := ⟨fun _ ↦ p.val, p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simps!]
noncomputable def Types.limitEquivFixedPoints :
    limit J ≃ MulAction.fixedPoints M (J.obj (SingleObj.star M)) :=
  (Types.limitEquivSections J).trans (Types.sections.equivFixedPoints J)

end Limits

section Colimits

variable {G : Type v} [Group G] (J : SingleObj G ⥤ Type u)

lemma Types.Quot.Rel.iff_orbitRel (x y : J.obj (SingleObj.star G)) :
    Types.Quot.Rel J ⟨SingleObj.star G, x⟩ ⟨SingleObj.star G, y⟩
    ↔ MulAction.orbitRel G (J.obj (SingleObj.star G)) x y := by
  have h (g : G) : y = g • x ↔ g • x = y := ⟨symm, symm⟩
  conv => rhs; rw [Setoid.comm']
  show (∃ g : G, y = g • x) ↔ (∃ g : G, g • x = y)
  conv => lhs; simp only [h]

@[simps]
def Types.Quot.equivOrbitRelQuotient :
    Types.Quot J ≃ MulAction.orbitRel.Quotient G (J.obj (SingleObj.star G)) where
  toFun := Quot.lift (fun p => ⟦p.2⟧) <| fun a b h => Quotient.sound <|
    (Types.Quot.Rel.iff_orbitRel J a.2 b.2).mp h
  invFun := Quot.lift (fun x => Quot.mk _ ⟨SingleObj.star G, x⟩) <| fun a b h =>
    Quot.sound <| (Types.Quot.Rel.iff_orbitRel J a b).mpr h
  left_inv := fun x => Quot.inductionOn x (fun _ ↦ rfl)
  right_inv := fun x => Quot.inductionOn x (fun _ ↦ rfl)

@[simps!]
noncomputable def Types.colimitEquivQuotient :
    colimit J ≃ MulAction.orbitRel.Quotient G (J.obj (SingleObj.star G)) :=
  (Types.colimitEquivQuot J).trans (Types.Quot.equivOrbitRelQuotient J)

end Colimits

end SingleObj

end Limits

end CategoryTheory
