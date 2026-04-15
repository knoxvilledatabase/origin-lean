/-
Extracted from NumberTheory/Padics/PadicIntegers.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# p-adic integers

This file defines the `p`-adic integers `ℤ_[p]` as the subtype of `ℚ_[p]` with norm `≤ 1`.
We show that `ℤ_[p]`
* is complete,
* is nonarchimedean,
* is a normed ring,
* is a local ring, and
* is a discrete valuation ring.

The relation between `ℤ_[p]` and `ZMod p` is established in another file.

## Important definitions

* `PadicInt` : the type of `p`-adic integers

## Notation

We introduce the notation `ℤ_[p]` for the `p`-adic integers.

## Implementation notes

Much, but not all, of this file assumes that `p` is prime. This assumption is inferred automatically
by taking `[Fact p.Prime]` as a type class argument.

Coercions into `ℤ_[p]` are set up to work with the `norm_cast` tactic.

## References

* [F. Q. Gouvêa, *p-adic numbers*][gouvea1997]
* [R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019]
* <https://en.wikipedia.org/wiki/P-adic_number>

## Tags

p-adic, p adic, padic, p-adic integer
-/

open Padic Metric IsLocalRing

noncomputable section

variable (p : ℕ) [hp : Fact p.Prime]

def PadicInt : Type := {x : ℚ_[p] // ‖x‖ ≤ 1}

notation "ℤ_[" p "]" => PadicInt p

namespace PadicInt

variable {p} {x y : ℤ_[p]}

/-! ### Ring structure and coercion to `ℚ_[p]` -/

-- INSTANCE (free from Core): :

theorem ext {x y : ℤ_[p]} : (x : ℚ_[p]) = y → x = y :=
  Subtype.ext

variable (p)

def subring : Subring ℚ_[p] where
  carrier := { x : ℚ_[p] | ‖x‖ ≤ 1 }
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' hx hy := (Padic.nonarchimedean _ _).trans <| max_le_iff.2 ⟨hx, hy⟩
  mul_mem' hx hy := (padicNormE.mul _ _).trans_le <| mul_le_one₀ hx (norm_nonneg _) hy
  neg_mem' hx := (norm_neg _).trans_le hx
