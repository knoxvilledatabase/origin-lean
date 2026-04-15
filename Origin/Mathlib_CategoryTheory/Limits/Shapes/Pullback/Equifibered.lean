/-
Extracted from CategoryTheory/Limits/Shapes/Pullback/Equifibered.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Equifibered natural transformation

## Main definition
- `CategoryTheory.NatTrans.Equifibered`:
  A natural transformation `α : F ⟶ G` is equifibered if every commutative square of the following
  form is a pullback.
  ```
  F(X) → F(Y)
   ↓      ↓
  G(X) → G(Y)
  ```
- `CategoryTheory.NatTrans.Coequifibered`: The dual notion.

-/

open CategoryTheory.Limits CategoryTheory.Functor

namespace CategoryTheory

variable {J K C D ι : Type*} [Category* J] [Category* C] [Category* K] [Category* D]

namespace NatTrans

def Equifibered : MorphismProperty (J ⥤ C) :=
  fun {F G} α ↦ ∀ ⦃i j : J⦄ (f : i ⟶ j), IsPullback (F.map f) (α.app i) (α.app j) (G.map f)

theorem Equifibered.of_isIso {F G : J ⥤ C} (α : F ⟶ G) [IsIso α] : Equifibered α :=
  fun _ _ f => IsPullback.of_vert_isIso ⟨naturality _ f⟩
