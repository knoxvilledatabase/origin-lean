/-
Extracted from CategoryTheory/Action/Continuous.lean
Genuine: 4 of 9 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!

# Topological subcategories of `Action V G`

For a concrete category `V`, where the forgetful functor factors via `TopCat`,
and a monoid `G`, equipped with a topological space instance,
we define the full subcategory `ContAction V G` of all objects of `Action V G`
where the induced action is continuous.

We also define a category `DiscreteContAction V G` as the full subcategory of `ContAction V G`,
where the underlying topological space is discrete.

Finally we define inclusion functors into `Action V G` and `TopCat` in terms
of `HasForget₂` instances.

-/

open CategoryTheory Limits

variable (V : Type*) [Category* V] {FV : V → V → Type*} {CV : V → Type*}
    [∀ X Y, FunLike (FV X Y) (CV X) (CV Y)] [ConcreteCategory V FV] [HasForget₂ V TopCat]

variable (G : Type*) [Monoid G] [TopologicalSpace G]

namespace Action

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): (X

variable {V G}

abbrev IsContinuous (X : Action V G) : Prop :=
  ContinuousSMul G ((CategoryTheory.forget₂ _ TopCat).obj X)

lemma isContinuous_def (X : Action V G) :
    X.IsContinuous ↔ Continuous (fun p : G × (forget₂ _ TopCat).obj X ↦
      (forget₂ _ TopCat).map (X.ρ p.1) p.2) :=
  ⟨fun h ↦ h.1, fun h ↦ ⟨h⟩⟩

end Action

open Action

abbrev ContAction : Type _ := ObjectProperty.FullSubcategory (IsContinuous (V := V) (G := G))

namespace ContAction

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

variable {V G}

abbrev IsDiscrete (X : ContAction V G) : Prop :=
  DiscreteTopology ((CategoryTheory.forget₂ _ TopCat).obj X)

variable (V) {H : Type*} [Monoid H] [TopologicalSpace H]
