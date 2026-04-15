/-
Extracted from CategoryTheory/GradedObject.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The category of graded objects

For any type `β`, a `β`-graded object over some category `C` is just
a function `β → C` into the objects of `C`.
We put the "pointwise" category structure on these, as the non-dependent specialization of
`CategoryTheory.Pi`.

We describe the `comap` functors obtained by precomposing with functions `β → γ`.

As a consequence a fixed element (e.g. `1`) in an additive group `β` provides a shift
functor on `β`-graded objects

When `C` has coproducts we construct the `total` functor `GradedObject β C ⥤ C`,
show that it is faithful, and deduce that when `C` is concrete so is `GradedObject β C`.

A covariant functoriality of `GradedObject β C` with respect to the index set `β` is also
introduced: if `p : I → J` is a map such that `C` has coproducts indexed by `p ⁻¹' {j}`, we
have a functor `map : GradedObject I C ⥤ GradedObject J C`.

-/

namespace CategoryTheory

open Category Limits

universe w v u

def GradedObject (β : Type w) (C : Type u) : Type max w u :=
  β → C

-- INSTANCE (free from Core): inhabitedGradedObject
