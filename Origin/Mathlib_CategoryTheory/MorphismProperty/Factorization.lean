/-
Extracted from CategoryTheory/MorphismProperty/Factorization.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The factorization axiom

In this file, we introduce a type-class `HasFactorization W₁ W₂`, which, given
two classes of morphisms `W₁` and `W₂` in a category `C`, asserts that any morphism
in `C` can be factored as a morphism in `W₁` followed by a morphism in `W₂`. The data
of such factorizations can be packaged in the type `FactorizationData W₁ W₂`.

This shall be used in the formalization of model categories for which the CM5 axiom
asserts that any morphism can be factored as a cofibration followed by a trivial
fibration (or a trivial cofibration followed by a fibration).

We also provide a structure `FunctorialFactorizationData W₁ W₂` which contains
the data of a functorial factorization as above. With this design, when we
formalize certain constructions (e.g. cylinder objects in model categories),
we may first construct them using the data `data : FactorizationData W₁ W₂`.
Without duplication of code, it shall be possible to show these cylinders
are functorial when a term `data : FunctorialFactorizationData W₁ W₂` is available,
the existence of which is asserted in the type-class `HasFunctorialFactorization W₁ W₂`.

We also introduce the class `W₁.comp W₂` of morphisms of the form `i ≫ p` with `W₁ i`
and `W₂ p` and show that `W₁.comp W₂ = ⊤` iff `HasFactorization W₁ W₂` holds (this
is `MorphismProperty.comp_eq_top_iff`).

-/

namespace CategoryTheory

namespace MorphismProperty

variable {C : Type*} [Category* C] (W₁ W₂ : MorphismProperty C)

structure MapFactorizationData {X Y : C} (f : X ⟶ Y) where
  /-- the intermediate object in the factorization -/
  Z : C
  /-- the first morphism in the factorization -/
  i : X ⟶ Z
  /-- the second morphism in the factorization -/
  p : Z ⟶ Y
  fac : i ≫ p = f := by cat_disch
  hi : W₁ i
  hp : W₂ p

namespace MapFactorizationData

attribute [reassoc (attr := simp)] fac

variable {X Y : C} (f : X ⟶ Y)
