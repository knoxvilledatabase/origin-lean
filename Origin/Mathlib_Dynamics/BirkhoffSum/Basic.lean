/-
Extracted from Dynamics/BirkhoffSum/Basic.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Birkhoff sums

In this file we define `birkhoffSum f g n x` to be the sum `∑ k ∈ Finset.range n, g (f^[k] x)`.
This sum (more precisely, the corresponding average `n⁻¹ • birkhoffSum f g n x`)
appears in various ergodic theorems
saying that these averages converge to the "space average" `⨍ x, g x ∂μ` in some sense.

See also `birkhoffAverage` defined in `Dynamics/BirkhoffSum/Average`.
-/

open Finset Function

section AddCommMonoid

variable {α M : Type*} [AddCommMonoid M]

def birkhoffSum (f : α → α) (g : α → M) (n : ℕ) (x : α) : M := ∑ k ∈ range n, g (f^[k] x)

theorem birkhoffSum_zero (f : α → α) (g : α → M) (x : α) : birkhoffSum f g 0 x = 0 :=
  sum_range_zero _
