/-
Extracted from CategoryTheory/Sites/Sieves.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Theory of sieves

- For an object `X` of a category `C`, a `Sieve X` is a predicate on morphisms to `X`
  which is closed under left-composition.
- The complete lattice structure on sieves is given, as well as the Galois insertion
  given by downward-closing.
- A `Sieve X` (functorially) induces a presheaf on `C` together with a monomorphism to
  the Yoneda embedding of `X`.

## Tags

sieve, pullback
-/

universe w w' v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Category Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)

variable {X Y Z : C} (f : Y ⟶ X)

def Presieve (X : C) :=
  ∀ ⦃Y⦄, (Y ⟶ X) → Prop

deriving CompleteLattice, Inhabited
