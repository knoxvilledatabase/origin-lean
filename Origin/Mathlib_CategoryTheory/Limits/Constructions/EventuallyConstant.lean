/-
Extracted from CategoryTheory/Limits/Constructions/EventuallyConstant.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Limits of eventually constant functors

If `F : J ⥤ C` is a functor from a cofiltered category, and `j : J`,
we introduce a property `F.IsEventuallyConstantTo j` which says
that for any `f : i ⟶ j`, the induced morphism `F.map f` is an isomorphism.
Under this assumption, it is shown that `F` admits `F.obj j` as a limit
(`Functor.IsEventuallyConstantTo.isLimitCone`).

A typeclass `Cofiltered.IsEventuallyConstant` is also introduced, and
the dual results for filtered categories and colimits are also obtained.

-/

namespace CategoryTheory

open Category Limits

variable {J C : Type*} [Category* J] [Category* C] (F : J ⥤ C)

namespace Functor

def IsEventuallyConstantTo (j : J) : Prop :=
  ∀ ⦃i : J⦄ (f : i ⟶ j), IsIso (F.map f)

def IsEventuallyConstantFrom (i : J) : Prop :=
  ∀ ⦃j : J⦄ (f : i ⟶ j), IsIso (F.map f)

namespace IsEventuallyConstantTo

variable {F} {i₀ : J} (h : F.IsEventuallyConstantTo i₀)

include h

lemma precomp {j : J} (f : j ⟶ i₀) : F.IsEventuallyConstantTo j :=
  fun _ φ ↦ h.isIso_map φ f

variable {i j : J} (φ : i ⟶ j) (hφ : Nonempty (j ⟶ i₀))
