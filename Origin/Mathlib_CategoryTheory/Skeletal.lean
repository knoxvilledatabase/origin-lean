/-
Extracted from CategoryTheory/Skeletal.lean
Genuine: 5 of 6 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Skeleton of a category

Define skeletal categories as categories in which any two isomorphic objects are equal.

Construct the skeleton of an arbitrary category by taking isomorphism classes, and show it is a
skeleton of the original category.

In addition, construct the skeleton of a thin category as a partial ordering, and (noncomputably)
show it is a skeleton of the original category. The advantage of this special case being handled
separately is that lemmas and definitions about orderings can be used directly, for example for the
subobject lattice. In addition, some of the commutative diagrams about the functors commute
definitionally on the nose which is convenient in practice.
-/

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Category

variable (C : Type u₁) [Category.{v₁} C]

variable (D : Type u₂) [Category.{v₂} D]

variable {E : Type u₃} [Category.{v₃} E]

def Skeletal : Prop :=
  ∀ ⦃X Y : C⦄, IsIsomorphic X Y → X = Y

structure IsSkeletonOf (F : D ⥤ C) : Prop where
  /-- The category `D` has isomorphic objects equal -/
  skel : Skeletal D
  /-- The functor `F` is an equivalence -/
  eqv : F.IsEquivalence := by infer_instance

attribute [local instance] isIsomorphicSetoid

variable {C D}

theorem Functor.eq_of_iso {F₁ F₂ : D ⥤ C} [Quiver.IsThin C] (hC : Skeletal C) (hF : F₁ ≅ F₂) :
    F₁ = F₂ :=
  Functor.ext (fun X => hC ⟨hF.app X⟩) fun _ _ _ => Subsingleton.elim _ _

theorem functor_skeletal [Quiver.IsThin C] (hC : Skeletal C) : Skeletal (D ⥤ C) := fun _ _ h =>
  h.elim (Functor.eq_of_iso hC)

variable (C D)

noncomputable section

def Skeleton : Type u₁ := InducedCategory (C := Quotient (isIsomorphicSetoid C)) C Quotient.out

deriving

  Category,

  [Inhabited C] → Inhabited _

set_option backward.inferInstanceAs.wrap.data false in

-- INSTANCE (free from Core): (α

end
