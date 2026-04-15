/-
Extracted from CategoryTheory/PathCategory/Basic.lean
Genuine: 1 of 4 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# The category paths on a quiver.
When `C` is a quiver, `paths C` is the category of paths.

## When the quiver is itself a category
We provide `path_composition : paths C ⥤ C`.

We check that the quotient of the path category of a category by the canonical relation
(paths are related if they compose to the same path) is equivalent to the original category.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

def Paths (V : Type u₁) : Type u₁ := V

-- INSTANCE (free from Core): (V

-- INSTANCE (free from Core): (V

variable (V : Type u₁) [Quiver.{v₁} V]

namespace Paths

-- INSTANCE (free from Core): categoryPaths
