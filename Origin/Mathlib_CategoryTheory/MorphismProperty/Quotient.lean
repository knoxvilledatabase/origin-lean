/-
Extracted from CategoryTheory/MorphismProperty/Quotient.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Classes of morphisms induced on quotient categories

Let `W : MorphismProperty C` and `homRel : HomRel C`. We assume that
`homRel` is stable under pre- and postcomposition. We introduce a property
`W.HasQuotient homRel` expressing that `W` induces a property of
morphisms on the quotient category, i.e. `W f ↔ W g` when `homRel f g` holds.
We denote `W.quotient homRel : MorphismProperty (Quotient homRel)` the
induced property of morphisms: a morphism in `C` satisfies `W` iff
`(Quotient.functor homRel).map f` does.

-/

namespace CategoryTheory

namespace MorphismProperty

variable {C : Type*} [Category* C]

class HasQuotient (W : MorphismProperty C) (homRel : HomRel C)
    [HomRel.IsStableUnderPrecomp homRel]
    [HomRel.IsStableUnderPostcomp homRel] : Prop where
  iff (W) : ∀ ⦃X Y : C⦄ ⦃f g : X ⟶ Y⦄, homRel f g → (W f ↔ W g)

variable (W : MorphismProperty C) {homRel : HomRel C}
  [HomRel.IsStableUnderPrecomp homRel]
  [HomRel.IsStableUnderPostcomp homRel]

lemma HasQuotient.iff_of_eqvGen [W.HasQuotient homRel] {X Y : C} {f g : X ⟶ Y}
    (h : Relation.EqvGen (@homRel _ _) f g) : W f ↔ W g := by
  induction h with
  | rel _ _ h => exact iff W h
  | refl => rfl
  | symm _ _ _ h => exact h.symm
  | trans _ _ _ _ _ h₁ h₂ => exact h₁.trans h₂

variable (homRel)
