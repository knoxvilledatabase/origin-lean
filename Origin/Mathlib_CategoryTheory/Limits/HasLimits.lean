/-
Extracted from CategoryTheory/Limits/HasLimits.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Existence of limits and colimits

In `CategoryTheory.Limits.IsLimit` we defined `IsLimit c`,
the data showing that a cone `c` is a limit cone.

The two main structures defined in this file are:
* `LimitCone F`, which consists of a choice of cone for `F` and the fact it is a limit cone, and
* `HasLimit F`, asserting the mere existence of some limit cone for `F`.

`HasLimit` is a propositional typeclass
(it's important that it is a proposition merely asserting the existence of a limit,
as otherwise we would have non-defeq problems from incompatible instances).

While `HasLimit` only asserts the existence of a limit cone,
we happily use the axiom of choice in mathlib,
so there are convenience functions all depending on `HasLimit F`:
* `limit F : C`, producing some limit object (of course all such are isomorphic)
* `limit.π F j : limit F ⟶ F.obj j`, the morphisms out of the limit,
* `limit.lift F c : c.pt ⟶ limit F`, the universal morphism from any other `c : Cone F`, etc.

Key to using the `HasLimit` interface is that there is an `@[ext]` lemma stating that
to check `f = g`, for `f g : Z ⟶ limit F`, it suffices to check `f ≫ limit.π F j = g ≫ limit.π F j`
for every `j`.
This, combined with `@[simp]` lemmas, makes it possible to prove many easy facts about limits using
automation (e.g. `tidy`).

There are abbreviations `HasLimitsOfShape J C` and `HasLimits C`
asserting the existence of classes of limits.
Later more are introduced, for finite limits, special shapes of limits, etc.

Ideally, many results about limits should be stated first in terms of `IsLimit`,
and then a result in terms of `HasLimit` derived from this.
At this point, however, this is far from uniformly achieved in mathlib ---
often statements are only written in terms of `HasLimit`.

## Implementation
At present we simply say everything twice, in order to handle both limits and colimits.
It would be highly desirable to have some automation support,
e.g. a `@[dualize]` attribute that behaves similarly to `@[to_additive]`.

## References
* [Stacks: Limits and colimits](https://stacks.math.columbia.edu/tag/002D)

-/

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Functor Opposite

namespace CategoryTheory.Limits

universe v₁ u₁ v₂ u₂ v₃ u₃ v v' v'' u u' u''

variable {J : Type u₁} [Category.{v₁} J] {K : Type u₂} [Category.{v₂} K]

variable {C : Type u} [Category.{v} C]

variable {F : J ⥤ C}

section Limit

structure LimitCone (F : J ⥤ C) where
  /-- The cone itself -/
  cone : Cone F
  /-- The proof that is the limit cone -/
  isLimit : IsLimit cone

class HasLimit (F : J ⥤ C) : Prop where mk' ::
  /-- There is some limit cone for `F` -/
  exists_limit : Nonempty (LimitCone F)

theorem HasLimit.mk {F : J ⥤ C} (d : LimitCone F) : HasLimit F :=
  ⟨Nonempty.intro d⟩

def getLimitCone (F : J ⥤ C) [HasLimit F] : LimitCone F :=
  Classical.choice <| HasLimit.exists_limit

variable (J C)

class HasLimitsOfShape : Prop where
  /-- All functors `F : J ⥤ C` from `J` have limits -/
  has_limit : ∀ F : J ⥤ C, HasLimit F := by infer_instance
