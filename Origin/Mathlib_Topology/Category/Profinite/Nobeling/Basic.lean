/-
Extracted from Topology/Category/Profinite/Nobeling/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Preliminaries for Nöbeling's theorem

This file constructs basic objects and results concerning them that are needed in the proof of
Nöbeling's theorem, which is in `Mathlib/Topology/Category/Profinite/Nobeling/Induction.lean`.
See the section docstrings for more information.

## Proof idea

We follow the proof of theorem 5.4 in [scholze2019condensed], in which the idea is to embed `S` in
a product of `I` copies of `Bool` for some sufficiently large `I`, and then to choose a
well-ordering on `I` and use ordinal induction over that well-order. Here we can let `I` be
the set of clopen subsets of `S` since `S` is totally separated.

The above means it suffices to prove the following statement: For a closed subset `C` of `I → Bool`,
the `ℤ`-module `LocallyConstant C ℤ` is free.

For `i : I`, let `e C i : LocallyConstant C ℤ` denote the map `fun f ↦ (if f.val i then 1 else 0)`.

The basis will consist of products `e C iᵣ * ⋯ * e C i₁` with `iᵣ > ⋯ > i₁` which cannot be written
as linear combinations of lexicographically smaller products. We call this set `GoodProducts C`.

What is proved by ordinal induction (in
`Mathlib/Topology/Category/Profinite/Nobeling/ZeroLimit.lean` and
`Mathlib/Topology/Category/Profinite/Nobeling/Successor.lean`) is that this set is linearly
independent. The fact that it spans is proved directly in
`Mathlib/Topology/Category/Profinite/Nobeling/Span.lean`.

## References

- [scholze2019condensed], Theorem 5.4.
-/

open CategoryTheory ContinuousMap Limits Opposite Submodule

universe u

namespace Profinite.NobelingProof

variable {I : Type u} (C : Set (I → Bool))

section Projections

/-!
## Projection maps

The purpose of this section is twofold.

Firstly, in the proof that the set `GoodProducts C` spans the whole module `LocallyConstant C ℤ`,
we need to project `C` down to finite discrete subsets and write `C` as a cofiltered limit of those.

Secondly, in the inductive argument, we need to project `C` down to "smaller" sets satisfying the
inductive hypothesis.

In this section we define the relevant projection maps and prove some compatibility results.

### Main definitions

* Let `J : I → Prop`. Then `Proj J : (I → Bool) → (I → Bool)` is the projection mapping everything
  that satisfies `J i` to itself, and everything else to `false`.

* The image of `C` under `Proj J` is denoted `π C J` and the corresponding map `C → π C J` is called
  `ProjRestrict`. If `J` implies `K` we have a map `ProjRestricts : π C K → π C J`.

* `spanCone_isLimit` establishes that when `C` is compact, it can be written as a limit of its
  images under the maps `Proj (· ∈ s)` where `s : Finset I`.
-/

variable (J K L : I → Prop) [∀ i, Decidable (J i)] [∀ i, Decidable (K i)] [∀ i, Decidable (L i)]

def Proj : (I → Bool) → (I → Bool) :=
  fun c i ↦ if J i then c i else false
