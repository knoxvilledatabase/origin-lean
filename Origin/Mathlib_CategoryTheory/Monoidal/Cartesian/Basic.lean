/-
Extracted from CategoryTheory/Monoidal/Cartesian/Basic.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Categories with chosen finite products

We introduce a class, `CartesianMonoidalCategory`, which bundles explicit choices
for a terminal object and binary products in a category `C`.
This is primarily useful for categories which have finite products with good
definitional properties, such as the category of types.

For better defeqs, we also extend `MonoidalCategory`.

## Implementation notes

For Cartesian monoidal categories, the oplax-monoidal/monoidal/braided structure of a functor `F`
preserving finite products is uniquely determined. See the `ofChosenFiniteProducts` declarations.

We however develop the theory for any `F.OplaxMonoidal`/`F.Monoidal`/`F.Braided` instance instead of
requiring it to be the `ofChosenFiniteProducts` one. This is to avoid diamonds: Consider
e.g. `𝟭 C` and `F ⋙ G`.

In applications requiring a finite-product-preserving functor to be
oplax-monoidal/monoidal/braided, avoid `attribute [local instance] ofChosenFiniteProducts` but
instead turn on the corresponding `ofChosenFiniteProducts` declaration for that functor only.

## Projects

- Construct an instance of chosen finite products in the category of affine scheme, using
  the tensor product.
- Construct chosen finite products in other categories appearing "in nature".

-/

namespace CategoryTheory

universe v v₁ v₂ v₃ u u₁ u₂ u₃

open MonoidalCategory Limits

class SemiCartesianMonoidalCategory (C : Type u) [Category.{v} C] extends MonoidalCategory C where
  /-- The tensor unit is a terminal object. -/
  isTerminalTensorUnit : IsTerminal (𝟙_ C)
  /-- The first projection from the product. -/
  fst (X Y : C) : X ⊗ Y ⟶ X
  /-- The second projection from the product. -/
  snd (X Y : C) : X ⊗ Y ⟶ Y
  fst_def (X Y : C) : fst X Y = X ◁ isTerminalTensorUnit.from Y ≫ (ρ_ X).hom := by cat_disch
  snd_def (X Y : C) : snd X Y = isTerminalTensorUnit.from X ▷ Y ≫ (λ_ Y).hom := by cat_disch

namespace SemiCartesianMonoidalCategory

variable {C : Type u} [Category.{v} C] [SemiCartesianMonoidalCategory C]

def toUnit (X : C) : X ⟶ 𝟙_ C := isTerminalTensorUnit.from X

-- INSTANCE (free from Core): (X
