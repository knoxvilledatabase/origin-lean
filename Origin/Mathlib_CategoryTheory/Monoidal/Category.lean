/-
Extracted from CategoryTheory/Monoidal/Category.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Monoidal categories

A monoidal category is a category equipped with a tensor product, unitors, and an associator.
In the definition, we provide the tensor product as a pair of functions
* `tensorObj : C → C → C`
* `tensorHom : (X₁ ⟶ Y₁) → (X₂ ⟶ Y₂) → ((X₁ ⊗ X₂) ⟶ (Y₁ ⊗ Y₂))`

and allow use of the overloaded notation `⊗` for both.
The unitors and associator are provided componentwise.

The tensor product can be expressed as a functor via `tensor : C × C ⥤ C`.
The unitors and associator are gathered together as natural
isomorphisms in `leftUnitor_nat_iso`, `rightUnitor_nat_iso` and `associator_nat_iso`.

Some consequences of the definition are proved in other files after proving the coherence theorem,
e.g. `(λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom` in `CategoryTheory.Monoidal.CoherenceLemmas`.

## Implementation notes

In the definition of monoidal categories, we also provide the whiskering operators:
* `whiskerLeft (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) : X ⊗ Y₁ ⟶ X ⊗ Y₂`, denoted by `X ◁ f`,
* `whiskerRight {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) : X₁ ⊗ Y ⟶ X₂ ⊗ Y`, denoted by `f ▷ Y`.

These are products of an object and a morphism (the terminology "whiskering"
is borrowed from 2-category theory). The tensor product of morphisms `tensorHom` can be defined
in terms of the whiskerings. There are two possible such definitions, which are related by
the exchange property of the whiskerings. These two definitions are accessed by `tensorHom_def`
and `tensorHom_def'`. By default, `tensorHom` is defined so that `tensorHom_def` holds
definitionally.

If you want to provide `tensorHom` and define `whiskerLeft` and `whiskerRight` in terms of it,
you can use the alternative constructor `CategoryTheory.MonoidalCategory.ofTensorHom`.

The whiskerings are useful when considering simp-normal forms of morphisms in monoidal categories.

### Simp-normal form for morphisms

Rewriting involving associators and unitors could be very complicated. We try to ease this
complexity by putting carefully chosen simp lemmas that rewrite any morphisms into the simp-normal
form defined below. Rewriting into simp-normal form is especially useful in preprocessing
performed by the `coherence` tactic.

The simp-normal form of morphisms is defined to be an expression that has the minimal number of
parentheses. More precisely,
1. it is a composition of morphisms like `f₁ ≫ f₂ ≫ f₃ ≫ f₄ ≫ f₅` such that each `fᵢ` is
  either a structural morphism (morphisms made up only of identities, associators, unitors)
  or a non-structural morphism, and
2. each non-structural morphism in the composition is of the form `X₁ ◁ X₂ ◁ X₃ ◁ f ▷ X₄ ▷ X₅`,
  where each `Xᵢ` is an object that is not the identity or a tensor and `f` is a non-structural
  morphism that is not the identity or a composite.

Note that `X₁ ◁ X₂ ◁ X₃ ◁ f ▷ X₄ ▷ X₅` is actually `X₁ ◁ (X₂ ◁ (X₃ ◁ ((f ▷ X₄) ▷ X₅)))`.

Currently, the simp lemmas don't rewrite `𝟙 X ⊗ₘ f` and `f ⊗ₘ 𝟙 Y` into `X ◁ f` and `f ▷ Y`,
respectively, since it requires a huge refactoring. We hope to add these simp lemmas soon.

## References
* Tensor categories, Etingof, Gelaki, Nikshych, Ostrik,
  http://www-math.mit.edu/~etingof/egnobookfinal.pdf
* <https://stacks.math.columbia.edu/tag/0FFK>.
-/

universe v u

open CategoryTheory.Category

open CategoryTheory.Iso

namespace CategoryTheory

class MonoidalCategoryStruct (C : Type u) [𝒞 : Category.{v} C] where
  /-- curried tensor product of objects -/
  tensorObj : C → C → C
  /-- left whiskering for morphisms -/
  whiskerLeft (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) : tensorObj X Y₁ ⟶ tensorObj X Y₂
  /-- right whiskering for morphisms -/
  whiskerRight {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) : tensorObj X₁ Y ⟶ tensorObj X₂ Y
  /-- Tensor product of identity maps is the identity: `𝟙 X₁ ⊗ₘ 𝟙 X₂ = 𝟙 (X₁ ⊗ X₂)` -/
  -- By default, it is defined in terms of whiskerings.
  tensorHom {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : (tensorObj X₁ X₂ ⟶ tensorObj Y₁ Y₂) :=
    whiskerRight f X₂ ≫ whiskerLeft Y₁ g
  /-- The tensor unity in the monoidal structure `𝟙_ C` -/
  tensorUnit (C) : C
  /-- The associator isomorphism `(X ⊗ Y) ⊗ Z ≃ X ⊗ (Y ⊗ Z)` -/
  associator : ∀ X Y Z : C, tensorObj (tensorObj X Y) Z ≅ tensorObj X (tensorObj Y Z)
  /-- The left unitor: `𝟙_ C ⊗ X ≃ X` -/
  leftUnitor : ∀ X : C, tensorObj tensorUnit X ≅ X
  /-- The right unitor: `X ⊗ 𝟙_ C ≃ X` -/
  rightUnitor : ∀ X : C, tensorObj X tensorUnit ≅ X

namespace MonoidalCategory

export MonoidalCategoryStruct

  (tensorObj whiskerLeft whiskerRight tensorHom tensorUnit associator leftUnitor rightUnitor)

end MonoidalCategory

namespace MonoidalCategory

scoped infixr:70 " ⊗ " => MonoidalCategoryStruct.tensorObj

scoped infixr:81 " ◁ " => MonoidalCategoryStruct.whiskerLeft

scoped infixl:81 " ▷ " => MonoidalCategoryStruct.whiskerRight

scoped infixr:70 " ⊗ₘ " => MonoidalCategoryStruct.tensorHom

scoped notation "𝟙_ " C:arg => MonoidalCategoryStruct.tensorUnit C

scoped notation "α_" => MonoidalCategoryStruct.associator

scoped notation "λ_" => MonoidalCategoryStruct.leftUnitor

scoped notation "ρ_" => MonoidalCategoryStruct.rightUnitor

def Pentagon {C : Type u} [Category.{v} C] [MonoidalCategoryStruct C]
    (Y₁ Y₂ Y₃ Y₄ : C) : Prop :=
  (α_ Y₁ Y₂ Y₃).hom ▷ Y₄ ≫ (α_ Y₁ (Y₂ ⊗ Y₃) Y₄).hom ≫ Y₁ ◁ (α_ Y₂ Y₃ Y₄).hom =
    (α_ (Y₁ ⊗ Y₂) Y₃ Y₄).hom ≫ (α_ Y₁ Y₂ (Y₃ ⊗ Y₄)).hom

end MonoidalCategory

open MonoidalCategory
