/-
Extracted from CategoryTheory/CopyDiscardCategory/Deterministic.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Deterministic Morphisms in Copy-Discard Categories

Morphisms that preserve the copy operation perfectly.

A morphism `f : X → Y` is deterministic if copying then applying `f` to both copies equals applying
`f` then copying: `f ≫ Δ[Y] = Δ[X] ≫ (f ⊗ f)`.

In probabilistic settings, these are morphisms without randomness. In cartesian categories, all
morphisms are deterministic.

## Main definitions

* `Deterministic` - Type class for morphisms that preserve copying

## Main results

* Identity morphisms are deterministic
* Composition of deterministic morphisms is deterministic

## Tags

deterministic, copy-discard category, comonoid morphism
-/

universe v u

namespace CategoryTheory

open MonoidalCategory ComonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [CopyDiscardCategory.{v} C]

abbrev Deterministic {X Y : C} (f : X ⟶ Y) := IsComonHom f

namespace Deterministic

variable {X Y Z : C}

lemma copy_natural (f : X ⟶ Y) [Deterministic f] : f ≫ Δ[Y] = Δ[X] ≫ (f ⊗ₘ f) :=
  IsComonHom.hom_comul f

lemma discard_natural (f : X ⟶ Y) [Deterministic f] : f ≫ ε[Y] = ε[X] :=
  IsComonHom.hom_counit f

end Deterministic

end CategoryTheory
