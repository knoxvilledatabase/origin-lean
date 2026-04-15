/-
Extracted from Dynamics/TopologicalEntropy/CoverEntropy.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Topological entropy via covers
We implement Bowen-Dinaburg's definitions of the topological entropy, via covers.

All is stated in the vocabulary of uniform spaces. For compact spaces, the uniform structure
is canonical, so the topological entropy depends only on the topological structure. This will give
a clean proof that the topological entropy is a topological invariant of the dynamics.

A notable choice is that we define the topological entropy of a subset `F` of the whole space.
Usually, one defines the entropy of an invariant subset `F` as the entropy of the restriction of the
transformation to `F`. We avoid the latter definition as it would involve frequent manipulation of
subtypes. Our version directly gives a meaning to the topological entropy of a subsystem, and a
single theorem (`subset_restriction_entropy` in `TopologicalEntropy.Semiconj`) will give the
equivalence between both versions.

Another choice is to give a meaning to the entropy of `∅` (it must be `-∞` to stay coherent) and to
keep the possibility for the entropy to be infinite. Hence, the entropy takes values in the extended
reals `[-∞, +∞]`. The consequence is that we use `ℕ∞`, `ℝ≥0∞` and `EReal` numbers.

## Main definitions
- `IsDynCoverOf`: property that dynamical balls centered on a subset `s` cover a subset `F`.
- `coverMincard`: minimal cardinality of a dynamical cover. Takes values in `ℕ∞`.
- `coverEntropyInfEntourage`/`coverEntropyEntourage`: exponential growth of `coverMincard`.
  The former is defined with a `liminf`, the later with a `limsup`. Take values in `EReal`.
- `coverEntropyInf`/`coverEntropy`: supremum of `coverEntropyInfEntourage`/`coverEntropyEntourage`
  over all entourages (or limit as the entourages go to the diagonal). These are Bowen-Dinaburg's
  versions of the topological entropy with covers. Take values in `EReal`.

## Implementation notes
There are two competing definitions of topological entropy in this file: one uses a `liminf`,
the other a `limsup`. These two topological entropies are equal as soon as they are applied to an
invariant subset by theorem `coverEntropyInf_eq_coverEntropy`. We choose the default definition
to be the definition using a `limsup`, and give it the simpler name `coverEntropy` (instead of
`coverEntropySup`). Theorems about the topological entropy of invariant subsets will be stated
using only `coverEntropy`.

## Main results
- `IsDynCoverOf.iterate_le_pow`: given a dynamical cover at time `n`, creates dynamical covers
  at all iterates `n * m` with controlled cardinality.
- `IsDynCoverOf.coverEntropyEntourage_le_log_card_div`: upper bound on `coverEntropyEntourage`
  given any dynamical cover.
- `coverEntropyInf_eq_coverEntropy`: equality between the notions of topological entropy defined
  with a `liminf` and a `limsup`.

## Tags
cover, entropy

## TODO
Get versions of the topological entropy on (pseudo-e)metric spaces.
-/

open Set SetRel Uniformity UniformSpace

open scoped Finset

namespace Dynamics

variable {X : Type*} {T : X → X} {U V : SetRel X X} {n : ℕ} {F s : Set X} {m n : ℕ}

/-! ### Dynamical covers -/

def IsDynCoverOf (T : X → X) (F : Set X) (U : SetRel X X) (n : ℕ) (s : Set X) : Prop :=
  IsCover (dynEntourage T U n) F s
