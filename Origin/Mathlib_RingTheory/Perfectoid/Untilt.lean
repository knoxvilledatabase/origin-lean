/-
Extracted from RingTheory/Perfectoid/Untilt.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Untilt Function

In this file, we define the untilt function from the pretilt of a
`p`-adically complete ring to the ring itself. Note that this
is not the untilt *functor*.

## Main definition
* `PreTilt.untilt` : Given a `p`-adically complete ring `O`, this is the
  multiplicative map from `PreTilt O p` to `O` itself. Specifically, it is
  defined as the limit of `p^n`-th powers of arbitrary lifts in `O` of the
  `n`-th component from the perfection of `O/p`.

## Main theorem
* `PreTilt.mk_untilt_eq_coeff_zero` : The composition of the mod `p` map
  with the untilt function equals taking the zeroth component of the perfection.

## Reference
* [Berkeley Lectures on \( p \)-adic Geometry][MR4446467]

## Tags
Perfectoid, Tilting equivalence, Untilt
-/

open Ideal Perfection

namespace PreTilt

variable {O : Type*} [CommRing O] {p : ℕ} [Fact (Nat.Prime p)] [Fact ¬IsUnit (p : O)]

variable [IsAdicComplete (span {(p : O)}) O]

noncomputable def untilt : PreTilt O p →* O :=
  teichmuller p _
