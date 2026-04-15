/-
Extracted from CategoryTheory/Sites/DenseSubsite/InducedTopology.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Induced Topology

We say that a functor `G : C ⥤ (D, K)` is locally dense if for each covering sieve `T` in `D` of
some `X : C`, `T ∩ mor(C)` generates a covering sieve of `X` in `D`. A locally dense fully faithful
functor then induces a topology on `C` via `{ T ∩ mor(C) | T ∈ K }`. Note that this is equal to
the collection of sieves on `C` whose image generates a covering sieve. This construction would
make `C` both cover-lifting and cover-preserving.

Some typical examples are full and cover-dense functors (for example the functor from a basis of a
topological space `X` into `Opens X`). The functor `Over X ⥤ C` is also locally dense, and the
induced topology can then be used to construct the big sites associated to a scheme.

Given a fully faithful cover-dense functor `G : C ⥤ (D, K)` between small sites, we then have
`Sheaf (H.inducedTopology) A ≌ Sheaf K A`. This is known as the comparison lemma.

## References

* [Elephant]: *Sketches of an Elephant*, P. T. Johnstone: C2.2.
* https://ncatlab.org/nlab/show/dense+sub-site
* https://ncatlab.org/nlab/show/comparison+lemma

-/

namespace CategoryTheory

universe v u

open Limits Opposite Presieve CategoryTheory

variable {C : Type*} [Category* C] {D : Type*} [Category* D] (G : C ⥤ D)

variable {J : GrothendieckTopology C} (K : GrothendieckTopology D)

variable (A : Type v) [Category.{u} A]

namespace Functor

class LocallyCoverDense : Prop where
  functorPushforward_functorPullback_mem :
    ∀ ⦃X : C⦄ (T : K (G.obj X)), (T.val.functorPullback G).functorPushforward G ∈ K (G.obj X)

variable [G.LocallyCoverDense K]

theorem pushforward_cover_iff_cover_pullback [G.Full] [G.Faithful] {X : C} (S : Sieve X) :
    S.functorPushforward G ∈ K (G.obj X) ↔ ∃ T : K (G.obj X), T.val.functorPullback G = S := by
  constructor
  · intro hS
    exact ⟨⟨_, hS⟩, (Sieve.fullyFaithfulFunctorGaloisCoinsertion G X).u_l_eq S⟩
  · rintro ⟨T, rfl⟩
    exact LocallyCoverDense.functorPushforward_functorPullback_mem T

variable [G.IsLocallyFull K] [G.IsLocallyFaithful K]
