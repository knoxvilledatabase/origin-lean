/-
Extracted from CategoryTheory/Category/Factorisation.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The Factorisation Category of a Category

`Factorisation f` is the category containing as objects all factorisations of a morphism `f`.

We show that `Factorisation f` always has an initial and a terminal object.

TODO: Show that `Factorisation f` is isomorphic to a comma category in two ways.

TODO: Make `MonoFactorisation f` a special case of a `Factorisation f`.
-/

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

set_option linter.style.whitespace false in -- manual alignment is not recognised

structure Factorisation {X Y : C} (f : X ⟶ Y) where
  /-- The midpoint of the factorisation. -/
  mid : C
  /-- The morphism into the factorisation midpoint. -/
  ι   : X ⟶ mid
  /-- The morphism out of the factorisation midpoint. -/
  π   : mid ⟶ Y
  /-- The factorisation condition. -/
  ι_π : ι ≫ π = f := by cat_disch

attribute [reassoc (attr := simp)] Factorisation.ι_π

namespace Factorisation

variable {X Y : C} {f : X ⟶ Y}
