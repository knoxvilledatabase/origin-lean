/-
Extracted from CategoryTheory/Bicategory/CatEnriched.lean
Genuine: 2 of 7 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
# The strict bicategory associated to a Cat-enriched category

If `C` is a type with an `EnrichedCategory Cat C` structure, then it has hom-categories, whose
objects define 1-dimensional arrows on `C` and whose morphisms define 2-dimensional arrows between
these. The enriched category axioms equip this data with the structure of a strict bicategory.

We define a type alias `CatEnriched C` for a type `C` with an `EnrichedCategory Cat C` structure. We
provide this with an instance of a strict bicategory structure constructing
`Bicategory.Strict (CatEnriched C)`.

If `C` is a type with an `EnrichedOrdinaryCategory Cat C` structure, then it has an
`EnrichedCategory Cat C` structure, so the previous construction would again produce a strict
bicategory. However, in this setting `C` is also given a `Category C` structure, together with an
equivalence between this category and the underlying category of the `EnrichedCategory Cat C`, and
in examples the given category structure is the preferred one.

Thus, we define a type alias `CatEnrichedOrdinary C` for a type `C` with an
`EnrichedOrdinaryCategory Cat C` structure. We provide this with an instance of a strict bicategory
structure extending the category structure provided by the given instance `Category C` constructing
`Bicategory.Strict (CatEnrichedOrdinary C)`.

-/

universe u v u' v'

namespace CategoryTheory

open Category

variable {C : Type*} [EnrichedCategory Cat C]

def CatEnriched (C : Type*) := C

namespace CatEnriched

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): {X

def hComp {a b c : CatEnriched C} {f f' : a ⟶ b} {g g' : b ⟶ c}
    (η : f ⟶ f') (θ : g ⟶ g') : f ≫ g ⟶ f' ≫ g' := (eComp Cat a b c).toFunctor.map (η, θ)
