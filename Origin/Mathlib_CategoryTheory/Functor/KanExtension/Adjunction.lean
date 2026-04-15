/-
Extracted from CategoryTheory/Functor/KanExtension/Adjunction.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-! # The Kan extension functor

Given a functor `L : C ⥤ D`, we define the left Kan extension functor
`L.lan : (C ⥤ H) ⥤ (D ⥤ H)` which sends a functor `F : C ⥤ H` to its
left Kan extension along `L`. This is defined if all `F` have such
a left Kan extension. It is shown that `L.lan` is the left adjoint to
the functor `(D ⥤ H) ⥤ (C ⥤ H)` given by the precomposition
with `L` (see `Functor.lanAdjunction`).

Similarly, we define the right Kan extension functor
`L.ran : (C ⥤ H) ⥤ (D ⥤ H)` which sends a functor `F : C ⥤ H` to its
right Kan extension along `L`.

-/

namespace CategoryTheory

open Category Limits

namespace Functor

variable {C D : Type*} [Category* C] [Category* D] (L : C ⥤ D) {H : Type*} [Category* H]

section lan

variable [∀ (F : C ⥤ H), HasLeftKanExtension L F]

noncomputable def lan : (C ⥤ H) ⥤ (D ⥤ H) where
  obj F := leftKanExtension L F
  map {F₁ F₂} φ := descOfIsLeftKanExtension _ (leftKanExtensionUnit L F₁) _
    (φ ≫ leftKanExtensionUnit L F₂)

noncomputable def lanUnit : (𝟭 (C ⥤ H)) ⟶ L.lan ⋙ (whiskeringLeft C D H).obj L where
  app F := leftKanExtensionUnit L F
  naturality {F₁ F₂} φ := by ext; simp [lan]

-- INSTANCE (free from Core): (F

end

noncomputable def isPointwiseLeftKanExtensionLeftKanExtensionUnit
    (F : C ⥤ H) [HasPointwiseLeftKanExtension L F] :
    (LeftExtension.mk _ (L.leftKanExtensionUnit F)).IsPointwiseLeftKanExtension :=
  isPointwiseLeftKanExtensionOfIsLeftKanExtension (F := F) _ (leftKanExtensionUnit L F)

open CostructuredArrow

variable (F : C ⥤ H) [HasPointwiseLeftKanExtension L F]

noncomputable def leftKanExtensionObjIsoColimit [HasLeftKanExtension L F] (X : D) :
    (L.leftKanExtension F).obj X ≅ colimit (proj L X ⋙ F) :=
  LeftExtension.IsPointwiseLeftKanExtensionAt.isoColimit (F := F)
    (isPointwiseLeftKanExtensionLeftKanExtensionUnit L F X)

set_option backward.isDefEq.respectTransparency false in
