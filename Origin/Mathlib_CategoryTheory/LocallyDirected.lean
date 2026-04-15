/-
Extracted from CategoryTheory/LocallyDirected.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
## Locally directed gluing

We say that a diagram of sets is "locally directed" if for any `V, W ⊆ U` in the diagram,
`V ∩ W` is a union of elements in the diagram. Equivalently, for every `x ∈ U` in the diagram,
the set of elements containing `x` is directed (and hence the name).

This is the condition needed to show that a colimit (in `TopCat`) of open embeddings is the
gluing of the open sets. See `Mathlib/AlgebraicGeometry/Gluing.lean` for an actual application.
-/

namespace CategoryTheory

open Limits

variable {J : Type*} [Category* J]

class Functor.IsLocallyDirected (F : J ⥤ Type*) : Prop where
  cond (F) : ∀ {i j k} (fi : i ⟶ k) (fj : j ⟶ k) (xi : F.obj i) (xj : F.obj j),
    F.map fi xi = F.map fj xj → ∃ (l : J) (fli : l ⟶ i) (flj : l ⟶ j) (x : _),
      F.map fli x = xi ∧ F.map flj x = xj

alias Functor.exists_map_eq_of_isLocallyDirected := Functor.IsLocallyDirected.cond

-- INSTANCE (free from Core): (F

-- INSTANCE (free from Core): (F

end CategoryTheory
