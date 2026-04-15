/-
Extracted from CategoryTheory/FinCategory/AsType.lean
Genuine: 7 of 10 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core
import Mathlib.Data.Fintype.Card
import Mathlib.CategoryTheory.FinCategory.Basic

/-!
# Finite categories are equivalent to category in `Type 0`.
-/

universe w v u

open scoped Classical

noncomputable section

namespace CategoryTheory

namespace FinCategory

variable (α : Type*) [Fintype α] [SmallCategory α] [FinCategory α]

abbrev ObjAsType : Type :=
  InducedCategory α (Fintype.equivFin α).symm

instance {i j : ObjAsType α} : Fintype (i ⟶ j) :=
  FinCategory.fintypeHom ((Fintype.equivFin α).symm i) _

noncomputable def objAsTypeEquiv : ObjAsType α ≌ α :=
  (inducedFunctor (Fintype.equivFin α).symm).asEquivalence

abbrev AsType : Type :=
  Fin (Fintype.card α)

@[simps (config := .lemmasOnly) id comp]
noncomputable instance categoryAsType : SmallCategory (AsType α) where
  Hom i j := Fin (Fintype.card (@Quiver.Hom (ObjAsType α) _ i j))
  id _ := Fintype.equivFin _ (𝟙 _)
  comp f g := Fintype.equivFin _ ((Fintype.equivFin _).symm f ≫ (Fintype.equivFin _).symm g)

attribute [local simp] categoryAsType_id categoryAsType_comp

@[simps]
noncomputable def asTypeToObjAsType : AsType α ⥤ ObjAsType α where
  obj := id
  map {_ _} := (Fintype.equivFin _).symm

@[simps]
noncomputable def objAsTypeToAsType : ObjAsType α ⥤ AsType α where
  obj := id
  map {_ _} := Fintype.equivFin _

noncomputable def asTypeEquivObjAsType : AsType α ≌ ObjAsType α where
  functor := asTypeToObjAsType α
  inverse := objAsTypeToAsType α
  unitIso := NatIso.ofComponents Iso.refl
  counitIso := NatIso.ofComponents Iso.refl

noncomputable instance asTypeFinCategory : FinCategory (AsType α) where
  fintypeHom := fun _ _ => show Fintype (Fin _) from inferInstance

noncomputable def equivAsType : AsType α ≌ α :=
  (asTypeEquivObjAsType α).trans (objAsTypeEquiv α)

end FinCategory

end CategoryTheory
