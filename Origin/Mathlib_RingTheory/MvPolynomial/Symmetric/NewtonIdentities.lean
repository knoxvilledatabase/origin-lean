/-
Extracted from RingTheory/MvPolynomial/Symmetric/NewtonIdentities.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Newton's Identities

This file defines `MvPolynomial` power sums as a means of implementing Newton's identities. The
combinatorial proof, due to Zeilberger, defines for `k : ℕ` a subset `pairs` of
`(range k).powerset × range k` and a map `pairMap` such that `pairMap` is an involution on `pairs`,
and a map `weight` which identifies elements of `pairs` with the terms of the summation in Newton's
identities and which satisfies `weight ∘ pairMap = -weight`. The result therefore follows neatly
from an identity implemented in mathlib as `Finset.sum_involution`. Namely, we use
`Finset.sum_involution` to show that `∑ t ∈ pairs σ k, weight σ R k t = 0`. We then identify
`(-1) ^ k * k * esymm σ R k` with the terms of the weight sum for which `t.fst` has
cardinality `k`, and `(-1) ^ i * esymm σ R i * psum σ R (k - i)` with the terms of the weight sum
for which `t.fst` has cardinality `i` for `i < k`, and we thereby derive the main result
`(-1) ^ k * k * esymm σ R k + ∑ i ∈ range k, (-1) ^ i * esymm σ R i * psum σ R (k - i) = 0` (or
rather, two equivalent forms which provide direct definitions for `esymm` and `psum` in lower-degree
terms).

## Main declarations

* `MvPolynomial.mul_esymm_eq_sum`: a recurrence relation for the `k`th elementary
  symmetric polynomial in terms of lower-degree elementary symmetric polynomials and power sums.

* `MvPolynomial.psum_eq_mul_esymm_sub_sum`: a recurrence relation for the degree-`k` power sum
  in terms of lower-degree elementary symmetric polynomials and power sums.

## References

See [zeilberger1984] for the combinatorial proof of Newton's identities.
-/

open Equiv (Perm)

open MvPolynomial

noncomputable section

namespace MvPolynomial

open Finset Nat

namespace NewtonIdentities

variable (σ : Type*) (R : Type*) [CommRing R]

section DecidableEq

variable [DecidableEq σ]

private def pairMap (t : Finset σ × σ) : Finset σ × σ :=
  if h : t.snd ∈ t.fst then (t.fst.erase t.snd, t.snd) else (t.fst.cons t.snd h, t.snd)

private lemma pairMap_ne_self (t : Finset σ × σ) : pairMap σ t ≠ t := by
  rw [pairMap]
  split_ifs with h1
  all_goals by_contra ht; rw [← ht] at h1; simp_all

private lemma pairMap_of_snd_mem_fst {t : Finset σ × σ} (h : t.snd ∈ t.fst) :
    pairMap σ t = (t.fst.erase t.snd, t.snd) := by
  simp [pairMap, h]

private lemma pairMap_of_snd_notMem_fst {t : Finset σ × σ} (h : t.snd ∉ t.fst) :
    pairMap σ t = (t.fst.cons t.snd h, t.snd) := by
  simp [pairMap, h]
