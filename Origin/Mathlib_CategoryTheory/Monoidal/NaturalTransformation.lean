/-
Extracted from CategoryTheory/Monoidal/NaturalTransformation.lean
Genuine: 2 of 17 | Dissolved: 0 | Infrastructure: 15
-/
import Origin.Core

/-!
# Monoidal natural transformations

Natural transformations between (lax) monoidal functors must satisfy
an additional compatibility relation with the tensorators:
`F.μ X Y ≫ app (X ⊗ Y) = (app X ⊗ app Y) ≫ G.μ X Y`.

-/

open CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

open CategoryTheory.Category

open CategoryTheory.Functor

namespace CategoryTheory

open MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E]
  {E' : Type u₄} [Category.{v₄} E'] [MonoidalCategory E']

variable {F₁ F₂ F₃ : C ⥤ D} (τ : F₁ ⟶ F₂) [F₁.LaxMonoidal] [F₂.LaxMonoidal] [F₃.LaxMonoidal]

namespace NatTrans

open Functor.LaxMonoidal

class IsMonoidal : Prop where
  unit : ε F₁ ≫ τ.app (𝟙_ C) = ε F₂ := by cat_disch
  tensor (X Y : C) : μ F₁ _ _ ≫ τ.app (X ⊗ Y) = (τ.app X ⊗ₘ τ.app Y) ≫ μ F₂ _ _ := by cat_disch

namespace IsMonoidal

attribute [reassoc (attr := simp)] unit tensor

-- INSTANCE (free from Core): id

-- INSTANCE (free from Core): comp

-- INSTANCE (free from Core): hcomp

-- INSTANCE (free from Core): whiskerRight

-- INSTANCE (free from Core): whiskerLeft

-- INSTANCE (free from Core): (F

-- INSTANCE (free from Core): (F

-- INSTANCE (free from Core): (F

end IsMonoidal

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): {F

end NatTrans

namespace Iso

variable (e : F₁ ≅ F₂) [NatTrans.IsMonoidal e.hom]

-- INSTANCE (free from Core): :

end Iso

namespace Adjunction

variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal

namespace IsMonoidal

variable [F.Monoidal] [G.LaxMonoidal] [adj.IsMonoidal]

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): :

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): :

end IsMonoidal

namespace Equivalence

variable (e : C ≌ D) [e.functor.Monoidal] [e.inverse.Monoidal] [e.IsMonoidal]

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

end Equivalence

end Adjunction

namespace LaxMonoidalFunctor

structure Hom (F G : LaxMonoidalFunctor C D) where
  /-- the natural transformation between the underlying functors -/
  hom : F.toFunctor ⟶ G.toFunctor
  isMonoidal : NatTrans.IsMonoidal hom := by infer_instance

attribute [instance] Hom.isMonoidal

-- INSTANCE (free from Core): :
