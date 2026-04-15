/-
Extracted from CategoryTheory/ComposableArrows/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Composable arrows

If `C` is a category, the type of `n`-simplices in the nerve of `C` identifies
to the type of functors `Fin (n + 1) ⥤ C`, which can be thought of as families of `n` composable
arrows in `C`. In this file, we introduce and study this category `ComposableArrows C n`
of `n` composable arrows in `C`.

If `F : ComposableArrows C n`, we define `F.left` as the leftmost object, `F.right` as the
rightmost object, and `F.hom : F.left ⟶ F.right` is the canonical map.

The most significant definition in this file is the constructor
`F.precomp f : ComposableArrows C (n + 1)` for `F : ComposableArrows C n` and `f : X ⟶ F.left`:
"it shifts `F` towards the right and inserts `f` on the left". This `precomp` has
good definitional properties.

In the namespace `CategoryTheory.ComposableArrows`, we provide constructors
like `mk₁ f`, `mk₂ f g`, `mk₃ f g h` for `ComposableArrows C n` for small `n`.

TODO (@joelriou):
* construct some elements in `ComposableArrows m (Fin (n + 1))` for small `n`
  the precomposition with which shall induce functors
  `ComposableArrows C n ⥤ ComposableArrows C m` which correspond to simplicial operations
  (specifically faces) with good definitional properties (this might be necessary for
  up to `n = 7` in order to formalize spectral sequences following Verdier)

-/

set_option backward.privateInPublic true

/-!
New `simprocs` that run even in `dsimp` have caused breakages in this file.

(e.g. `dsimp` can now simplify `2 + 3` to `5`)

For now, we just turn off the offending simprocs in this file.

*However*, hopefully it is possible to refactor the material here so that no disabling of
simprocs is needed.

See issue https://github.com/leanprover-community/mathlib4/issues/27382.
-/

attribute [-simp] Fin.reduceFinMk

namespace CategoryTheory

open Category

variable (C : Type*) [Category* C]

abbrev ComposableArrows (n : ℕ) := Fin (n + 1) ⥤ C

namespace ComposableArrows

variable {C} {n m : ℕ}

variable (F G : ComposableArrows C n)

macro "valid" : tactic =>

  `(tactic| first | assumption | apply zero_le | apply le_rfl | transitivity <;> assumption | omega)
