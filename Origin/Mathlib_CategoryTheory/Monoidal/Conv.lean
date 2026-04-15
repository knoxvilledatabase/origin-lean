/-
Extracted from CategoryTheory/Monoidal/Conv.lean
Genuine: 1 of 6 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
# The convolution monoid.

When `M : Comon C` and `N : Mon C`, the morphisms `M.X ⟶ N.X` form a monoid (in Type).
-/

universe v₁ u₁

namespace CategoryTheory

open MonoidalCategory

open MonObj ComonObj

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

def Conv (M N : C) : Type v₁ := M ⟶ N

namespace Conv

variable {M : C} {N : C} [ComonObj M] [MonObj N]

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

end Conv

end CategoryTheory
