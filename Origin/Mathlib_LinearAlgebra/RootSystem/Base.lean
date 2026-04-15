/-
Extracted from LinearAlgebra/RootSystem/Base.lean
Genuine: 1 of 2 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-!
# Bases for root pairings / systems

This file contains a theory of bases for root pairings / systems.

## Implementation details

For reduced root pairings `RootSystem.Base` is equivalent to the usual definition appearing in the
informal literature (e.g., it follows from [serre1965](Ch. V, §8, Proposition 7) that
`RootSystem.Base` is equivalent to both [serre1965](Ch. V, §8, Definition 5) and
[bourbaki1968](Ch. VI, §1.5) for reduced pairings). However for non-reduced root pairings, it is
more restrictive because it includes axioms on coroots as well as on roots. For example by
`RootPairing.Base.eq_one_or_neg_one_of_mem_support_of_smul_mem` it is clear that the 1-dimensional
root system `{-2, -1, 0, 1, 2} ⊆ ℝ` has no base in the sense of `RootSystem.Base`.

It is also worth remembering that it is only for reduced root systems that one has the simply
transitive action of the Weyl group on the set of bases, and that the Weyl group of a non-reduced
root system is the same as that of the reduced root system obtained by passing to the indivisible
roots.

For infinite root systems, `RootSystem.Base` is usually not the right notion: linear independence
is too strong.

## Main definitions / results:
* `RootSystem.Base`: a base of a root pairing.
* `RootSystem.Base.IsPos`: the predicate that a (co)root is positive relative to a base.
* `RootSystem.Base.induction_add`: an induction principle for predicates on (co)roots which
  respect addition of a simple root.
* `RootSystem.Base.induction_reflect`: an induction principle for predicates on (co)roots which
  respect reflection in a simple root.

## TODO

* Develop a theory of base / separation / positive roots for infinite systems which specialises to
  the concept here for finite systems.

-/

noncomputable section

open Function Set Submodule

open FaithfulSMul (algebraMap_injective)

open Module

open End (invtSubmodule mem_invtSubmodule)

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace RootPairing

structure Base (P : RootPairing ι R M N) where
  /-- The indices of the simple roots / coroots. -/
  support : Finset ι
  linearIndepOn_root : LinearIndepOn R P.root support
  linearIndepOn_coroot : LinearIndepOn R P.coroot support
  root_mem_or_neg_mem (i : ι) : P.root i ∈ AddSubmonoid.closure (P.root '' support) ∨
                               -P.root i ∈ AddSubmonoid.closure (P.root '' support)
  coroot_mem_or_neg_mem (i : ι) : P.coroot i ∈ AddSubmonoid.closure (P.coroot '' support) ∨
                                 -P.coroot i ∈ AddSubmonoid.closure (P.coroot '' support)

namespace Base

section RootPairing

variable {P : RootPairing ι R M N} (b : P.Base)

-- DISSOLVED: support_nonempty
