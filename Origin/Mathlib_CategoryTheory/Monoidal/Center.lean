/-
Extracted from CategoryTheory/Monoidal/Center.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Half braidings and the Drinfeld center of a monoidal category

We define `Center C` to be pairs `⟨X, b⟩`, where `X : C` and `b` is a half-braiding on `X`.

We show that `Center C` is braided monoidal,
and provide the monoidal functor `Center.forget` from `Center C` back to `C`.

## Implementation notes

Verifying the various axioms directly requires tedious rewriting.
Using the `slice` tactic may make the proofs marginally more readable.

More exciting, however, would be to make possible one of the following options:
1. Integration with homotopy.io / globular to give "picture proofs".
2. The monoidal coherence theorem, so we can ignore associators
   (after which most of these proofs are trivial).
3. Automating these proofs using `rewrite_search` or some relative.

In this file, we take the second approach using the monoidal composition `⊗≫` and the
`coherence` tactic.
-/

universe v v₁ v₂ v₃ u u₁ u₂ u₃

noncomputable section

namespace CategoryTheory

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

structure HalfBraiding (X : C) where
  /-- The family of isomorphisms `X ⊗ U ≅ U ⊗ X` -/
  β : ∀ U, X ⊗ U ≅ U ⊗ X
  monoidal : ∀ U U', (β (U ⊗ U')).hom =
      (α_ _ _ _).inv ≫
        ((β U).hom ▷ U') ≫ (α_ _ _ _).hom ≫ (U ◁ (β U').hom) ≫ (α_ _ _ _).inv := by
    cat_disch
  naturality : ∀ {U U'} (f : U ⟶ U'), (X ◁ f) ≫ (β U').hom = (β U).hom ≫ (f ▷ X) := by
    cat_disch

attribute [reassoc, simp] HalfBraiding.monoidal -- the reassoc lemma is redundant as a simp lemma

attribute [simp, reassoc] HalfBraiding.naturality

variable (C)

def Center :=
  Σ X : C, HalfBraiding X

namespace Center

variable {C}
