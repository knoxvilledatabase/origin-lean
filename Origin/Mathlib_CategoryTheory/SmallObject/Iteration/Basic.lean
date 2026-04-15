/-
Extracted from CategoryTheory/SmallObject/Iteration/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Transfinite iterations of a successor structure

In this file, we introduce the structure `SuccStruct` on a category `C`.
It consists of the data of an object `X₀ : C`, a successor map `succ : C → C`
and a morphism `toSucc : X ⟶ succ X` for any `X : C`. The map `toSucc`
does not have to be natural in `X`. For any element `j : J` in a
well-ordered type `J`, we would like to define
the iteration of `Φ : SuccStruct C`, as a functor `F : J ⥤ C`
such that `F.obj ⊥ = X₀`, `F.obj j ⟶ F.obj (Order.succ j)` is `toSucc (F.obj j)`
when `j` is not maximal, and when `j` is limit, `F.obj j` should be the
colimit of the `F.obj k` for `k < j`.

In the small object argument, we shall apply this to the iteration of
a functor `F : C ⥤ C` equipped with a natural transformation `ε : 𝟭 C ⟶ F`:
this will correspond to the case of
`SuccStruct.ofNatTrans ε : SuccStruct (C ⥤ C)`, for which `X₀ := 𝟭 C`,
`succ G := G ⋙ F` and `toSucc G : G ⟶ G ⋙ F` is given by `whiskerLeft G ε`.

The construction of the iteration of `Φ : SuccStruct C` is done
by transfinite induction, under an assumption `HasIterationOfShape C J`.
However, for a limit element `j : J`, the definition of `F.obj j`
does not involve only the objects `F.obj i` for `i < j`, but it also
involves the maps `F.obj i₁ ⟶ F.obj i₂` for `i₁ ≤ i₂ < j`.
Then, this is not a straightforward application of definitions by
transfinite induction. In order to solve this technical difficulty,
we introduce a structure `Φ.Iteration j` for any `j : J`. This
structure contains all the expected data and properties for
all the indices that are `≤ j`. In this file, we show that
`Φ.Iteration j` is a subsingleton. The existence shall be
obtained in the file `Mathlib/CategoryTheory/SmallObject/Iteration/Nonempty.lean`, and
the construction of the functor `Φ.iterationFunctor J : J ⥤ C`
and of its colimit `Φ.iteration J : C` will be done in the
file `Mathlib/CategoryTheory/SmallObject/TransfiniteIteration.lean`.

The map `Φ.toSucc X : X ⟶ Φ.succ X` does not have to be natural
(and it is not in certain applications). Then, two isomorphic
objects `X` and `Y` may have non-isomorphic successors. This is
the reason why we make an extensive use of equalities in
`C` and in `Arrow C` in the definitions.

## Note

The iteration was first introduced in mathlib by Joël Riou, using
a different approach as the one described above. After refactoring
his code, he found that the approach described above had already
been used in the pioneering formalization work in Lean 3 by
Reid Barton in 2018 towards the model category structure on
topological spaces.

-/

universe w v v' u u'

namespace CategoryTheory

open Category Limits

namespace SmallObject

variable {C : Type u} [Category.{v} C] {J : Type w}

variable [PartialOrder J] {j : J} (F : Set.Iic j ⥤ C) {i : J} (hi : i ≤ j)

def restrictionLT : Set.Iio i ⥤ C :=
  (Set.principalSegIioIicOfLE hi).monotone.functor ⋙ F
