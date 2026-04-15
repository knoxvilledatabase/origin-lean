/-
Extracted from LinearAlgebra/RootSystem/Finite/G2.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Properties of the `𝔤₂` root system.

The `𝔤₂` root pairing is special enough to deserve its own API. We provide one in this file.

As an application we prove the key result that a crystallographic, reduced, irreducible root
pairing containing two roots of Coxeter weight three is spanned by this pair of roots (and thus
is two-dimensional). This result is usually proved only for pairs of roots belonging to a base (as a
corollary of the fact that no node can have degree greater than three) and moreover usually requires
stronger assumptions on the coefficients than here.

## Main results:
* `RootPairing.EmbeddedG2`: a data-bearing typeclass which distinguishes a pair of roots whose
  pairing is `-3` (equivalently, with a distinguished choice of base). This is a sufficient
  condition for the span of this pair of roots to be a `𝔤₂` root system.
* `RootPairing.IsG2`: a prop-valued typeclass characterising the `𝔤₂` root system.
* `RootPairing.IsNotG2`: a prop-valued typeclass stating that a crystallographic, reduced,
  irreducible root system is not `𝔤₂`.
* `RootPairing.EmbeddedG2.shortRoot`: the distinguished short root, which we often donate `α`
* `RootPairing.EmbeddedG2.longRoot`: the distinguished long root, which we often donate `β`
* `RootPairing.EmbeddedG2.shortAddLong`: the short root `α + β`
* `RootPairing.EmbeddedG2.twoShortAddLong`: the short root `2α + β`
* `RootPairing.EmbeddedG2.threeShortAddLong`: the long root `3α + β`
* `RootPairing.EmbeddedG2.threeShortAddTwoLong`: the long root `3α + 2β`
* `RootPairing.EmbeddedG2.span_eq_top`: a crystallographic reduced irreducible root pairing
  containing two roots with pairing `-3` is spanned by this pair (thus two-dimensional).
* `RootPairing.EmbeddedG2.card_index_eq_twelve`: the `𝔤₂` root pairing has twelve roots.

## TODO
Once sufficient API for `RootPairing.Base` has been developed:
* Add `def EmbeddedG2.toBase [P.EmbeddedG2] : P.Base` with `support := {long P, short P}`
* Given `P` satisfying `[P.IsG2]`, distinct elements of a base must pair to `-3` (in one order).

-/

noncomputable section

open FaithfulSMul Function Set Submodule

open List hiding mem_toFinset

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

namespace RootPairing

class EmbeddedG2 extends P.IsCrystallographic, P.IsReduced where
  /-- The distinguished long root of an embedded `𝔤₂` root pairing. -/
  long : ι
  /-- The distinguished short root of an embedded `𝔤₂` root pairing. -/
  short : ι
  pairingIn_long_short : P.pairingIn ℤ long short = -3

class IsG2 : Prop extends P.IsCrystallographic, P.IsReduced, P.IsIrreducible where
  exists_pairingIn_neg_three : ∃ i j, P.pairingIn ℤ i j = -3

class IsNotG2 : Prop extends P.IsCrystallographic, P.IsReduced, P.IsIrreducible where
  pairingIn_mem_zero_one_two (i j : ι) : P.pairingIn ℤ i j ∈ ({-2, -1, 0, 1, 2} : Set ℤ)

section IsG2
