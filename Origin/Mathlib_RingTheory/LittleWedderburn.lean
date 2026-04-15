/-
Extracted from RingTheory/LittleWedderburn.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Wedderburn's Little Theorem

This file proves Wedderburn's Little Theorem.

## Main Declarations

* `littleWedderburn`: a finite division ring is a field.

## Future work

A couple simple generalisations are possible:
* A finite ring is commutative iff all its nilpotents lie in the center.
  [Chintala, Vineeth, *Sorry, the Nilpotents Are in the Center*][chintala2020]
* A ring is commutative if all its elements have finite order.
  [Dolan, S. W., *A Proof of Jacobson's Theorem*][dolan1975]

When alternativity is added to Mathlib, one could formalise the Artin-Zorn theorem, which states
that any finite alternative division ring is in fact a field.
https://en.wikipedia.org/wiki/Artin%E2%80%93Zorn_theorem

If interested, generalisations to semifields could be explored. The theory of semi-vector spaces is
not clear, but assuming that such a theory could be found where every module considered in the
below proof is free, then the proof works nearly verbatim.

-/

open scoped Polynomial

open Fintype

/-! Everything in this namespace is internal to the proof of Wedderburn's little theorem. -/

namespace LittleWedderburn

variable (D : Type*) [DivisionRing D]

private def InductionHyp : Prop :=
  ∀ {R : Subring D}, R < ⊤ → ∀ ⦃x y⦄, x ∈ R → y ∈ R → x * y = y * x

namespace InductionHyp

open Module Polynomial

variable {D}
