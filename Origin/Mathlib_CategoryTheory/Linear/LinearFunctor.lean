/-
Extracted from CategoryTheory/Linear/LinearFunctor.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Linear Functors

An additive functor between two `R`-linear categories is called *linear*
if the induced map on hom types is a morphism of `R`-modules.

## Implementation details

`Functor.Linear` is a `Prop`-valued class, defined by saying that
for every two objects `X` and `Y`, the map
`F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)` is a morphism of `R`-modules.

-/

namespace CategoryTheory

variable (R : Type*) [Semiring R] {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [Preadditive D] [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
  (F : C ⥤ D)

class Functor.Linear : Prop where
  /-- the functor induces a linear map on morphisms -/
  map_smul : ∀ {X Y : C} (f : X ⟶ Y) (r : R), F.map (r • f) = r • F.map f := by cat_disch

lemma Functor.linear_iff (F : C ⥤ D) :
    Functor.Linear R F ↔ ∀ (X : C) (r : R), F.map (r • 𝟙 X) = r • 𝟙 (F.obj X) := by
  constructor
  · intro h X r
    rw [h.map_smul, F.map_id]
  · refine fun h => ⟨fun {X Y} f r => ?_⟩
    have : r • f = (r • 𝟙 X) ≫ f := by simp
    rw [this, F.map_comp, h, Linear.smul_comp, Category.id_comp]

section Linear

namespace Functor

variable {R} [Linear R F]
