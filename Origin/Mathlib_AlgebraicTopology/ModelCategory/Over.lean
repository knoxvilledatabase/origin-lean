/-
Extracted from AlgebraicTopology/ModelCategory/Over.lean
Genuine: 3 of 21 | Dissolved: 0 | Infrastructure: 18
-/
import Origin.Core

/-!
# The model category structure on Over categories

Let `C` be a model category. For any `S : C`, we define
a model category structure on the category `Over S`:
a morphism `X ⟶ Y` in `Over S` is a cofibration
(resp. a fibration, a weak equivalence) if the
underlying morphism `f.left : X.left ⟶ Y.left` is.
(Apart from the existence of (finite) limits
from `Mathlib.CategoryTheory.Limits.Constructions.Over.Basic`, the verification
of the axioms is straightforward.)

## TODO
* Proceed to the dual construction for `Under S`.

-/

universe v u

open CategoryTheory

variable {C : Type u} [Category.{v} C] (S : C)

namespace HomotopicalAlgebra

variable [CategoryWithCofibrations C]

-- INSTANCE (free from Core): :

lemma cofibrations_over_iff {X Y : Over S} (f : X ⟶ Y) :
    Cofibration f ↔ Cofibration f.left := by
  simp only [cofibration_iff, cofibrations_over_def, MorphismProperty.over_iff]

-- INSTANCE (free from Core): {X

-- INSTANCE (free from Core): [(cofibrations

end

variable [CategoryWithFibrations C]

-- INSTANCE (free from Core): :

lemma fibrations_over_iff {X Y : Over S} (f : X ⟶ Y) :
    Fibration f ↔ Fibration f.left := by
  simp only [fibration_iff, fibrations_over_def, MorphismProperty.over_iff]

-- INSTANCE (free from Core): {X

-- INSTANCE (free from Core): [(fibrations

end

variable [CategoryWithWeakEquivalences C]

-- INSTANCE (free from Core): :

lemma weakEquivalences_over_iff {X Y : Over S} (f : X ⟶ Y) :
    WeakEquivalence f ↔ WeakEquivalence f.left := by
  simp only [weakEquivalence_iff, weakEquivalences_over_def, MorphismProperty.over_iff]

-- INSTANCE (free from Core): {X

-- INSTANCE (free from Core): [(weakEquivalences

end

-- INSTANCE (free from Core): [CategoryWithWeakEquivalences

variable [CategoryWithWeakEquivalences C] [CategoryWithCofibrations C]
  [CategoryWithFibrations C]

-- INSTANCE (free from Core): [(trivialCofibrations

-- INSTANCE (free from Core): [(cofibrations

end

-- INSTANCE (free from Core): ModelCategory.over

end HomotopicalAlgebra
