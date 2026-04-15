/-
Extracted from CategoryTheory/Monoidal/Closed/Types.lean
Genuine: 1 of 4 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Cartesian closure of Type

Show that `Type u₁` is Cartesian closed, and `C ⥤ Type u₁` is Cartesian closed for `C` a small
category in `Type u₁`.
Note this implies that the category of presheaves on a small category `C` is Cartesian closed.
-/

namespace CategoryTheory

noncomputable section

open Category Limits MonoidalCategory

universe v₁ v₂ u₁ u₂

variable {C : Type v₂} [Category.{v₁} C]

section MonoidalClosed

def Types.tensorProductAdjunction (X : Type v₁) :
    tensorLeft X ⊣ coyoneda.obj (Opposite.op X) where
  unit := { app Z := TypeCat.ofHom fun z ↦ TypeCat.ofHom fun x => ⟨x, z⟩ }
  counit := { app _ := TypeCat.ofHom (fun xf => xf.2.hom xf.1) }

-- INSTANCE (free from Core): (X

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): {C

attribute [local instance] uliftCategory in
