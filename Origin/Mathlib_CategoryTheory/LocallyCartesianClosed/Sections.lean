/-
Extracted from CategoryTheory/LocallyCartesianClosed/Sections.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The section functor as a right adjoint to the toOver functor

We show that in a cartesian monoidal category `C`, for any exponentiable object `I`, the functor
`toOver I : C ⥤ Over I` mapping an object `X` to the projection `snd : X ⊗ I ⟶ I` in `Over I`
has a right adjoint `sections I : Over I ⥤ C` whose object part is the object of sections
of `X` over `I`.

In particular, if `C` is cartesian closed, then for all objects `I` in `C`, `toOver I : C ⥤ Over I`
has a right adjoint.

-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Limits MonoidalCategory CartesianMonoidalCategory MonoidalClosed

section Sections

variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C]

variable (I : C) [Closed I]

abbrev curryRightUnitorHom : 𝟙_ C ⟶ (I ⟶[C] I) :=
  curry <| (ρ_ _).hom

variable {I}

theorem toUnit_comp_curryRightUnitorHom {A : C} :
    toUnit A ≫ curryRightUnitorHom I = curry (fst I A) := by
  apply uncurry_injective
  simp [uncurry_natural_left, curryRightUnitorHom, fst_def, toUnit]

namespace Over

open ChosenPullbacksAlong

variable (I) [ChosenPullbacksAlong (curryRightUnitorHom I)]

set_option backward.isDefEq.respectTransparency false in
