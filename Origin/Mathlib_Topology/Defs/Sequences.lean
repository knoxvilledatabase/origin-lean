/-
Extracted from Topology/Defs/Sequences.lean
Genuine: 8 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Topology.Defs.Filter
import Mathlib.Order.Filter.AtTopBot

/-!
# Sequences in topological spaces

In this file we define sequential closure, continuity, compactness etc.

## Main definitions

### Set operation
* `seqClosure s`: sequential closure of a set, the set of limits of sequences of points of `s`;

### Predicates

* `IsSeqClosed s`: predicate saying that a set is sequentially closed, i.e., `seqClosure s ⊆ s`;
* `SeqContinuous f`: predicate saying that a function is sequentially continuous, i.e.,
  for any sequence `u : ℕ → X` that converges to a point `x`, the sequence `f ∘ u` converges to
  `f x`;
* `IsSeqCompact s`: predicate saying that a set is sequentially compact, i.e., every sequence
  taking values in `s` has a converging subsequence.

### Type classes

* `FrechetUrysohnSpace X`: a typeclass saying that a topological space is a *Fréchet-Urysohn
  space*, i.e., the sequential closure of any set is equal to its closure.
* `SequentialSpace X`: a typeclass saying that a topological space is a *sequential space*, i.e.,
  any sequentially closed set in this space is closed. This condition is weaker than being a
  Fréchet-Urysohn space.
* `SeqCompactSpace X`: a typeclass saying that a topological space is sequentially compact, i.e.,
  every sequence in `X` has a converging subsequence.

## Tags

sequentially closed, sequentially compact, sequential space
-/

open Set Filter

open scoped Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def seqClosure (s : Set X) : Set X :=
  { a | ∃ x : ℕ → X, (∀ n : ℕ, x n ∈ s) ∧ Tendsto x atTop (𝓝 a) }

def IsSeqClosed (s : Set X) : Prop :=
  ∀ ⦃x : ℕ → X⦄ ⦃p : X⦄, (∀ n, x n ∈ s) → Tendsto x atTop (𝓝 p) → p ∈ s

def SeqContinuous (f : X → Y) : Prop :=
  ∀ ⦃x : ℕ → X⦄ ⦃p : X⦄, Tendsto x atTop (𝓝 p) → Tendsto (f ∘ x) atTop (𝓝 (f p))

def IsSeqCompact (s : Set X) :=
  ∀ ⦃x : ℕ → X⦄, (∀ n, x n ∈ s) → ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a)

variable (X)

@[mk_iff]
class SeqCompactSpace : Prop where
  isSeqCompact_univ : IsSeqCompact (univ : Set X)

export SeqCompactSpace (isSeqCompact_univ)

class FrechetUrysohnSpace : Prop where
  closure_subset_seqClosure : ∀ s : Set X, closure s ⊆ seqClosure s

class SequentialSpace : Prop where
  isClosed_of_seq : ∀ s : Set X, IsSeqClosed s → IsClosed s

variable {X}

protected theorem IsSeqClosed.isClosed [SequentialSpace X] {s : Set X} (hs : IsSeqClosed s) :
    IsClosed s :=
  SequentialSpace.isClosed_of_seq s hs
