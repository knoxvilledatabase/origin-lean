/-
Extracted from RingTheory/Polynomial/UniqueFactorization.lean
Genuine: 2 of 5 | Dissolved: 1 | Infrastructure: 2
-/
import Origin.Core

/-!
# Unique factorization for univariate and multivariate polynomials

## Main results
* `Polynomial.wfDvdMonoid`:
  If an integral domain is a `WFDvdMonoid`, then so is its polynomial ring.
* `Polynomial.uniqueFactorizationMonoid`, `MvPolynomial.uniqueFactorizationMonoid`:
  If an integral domain is a `UniqueFactorizationMonoid`, then so is its polynomial ring (of any
  number of variables).
-/

noncomputable section

open Polynomial

universe u v

namespace Polynomial

variable {R : Type*} [CommSemiring R] [NoZeroDivisors R] [WfDvdMonoid R] {f : R[X]}

-- INSTANCE (free from Core): (priority

variable [Nontrivial R]

theorem exists_irreducible_of_degree_pos (hf : 0 < f.degree) : ∃ g, Irreducible g ∧ g ∣ f :=
  WfDvdMonoid.exists_irreducible_factor (fun huf => ne_of_gt hf <| degree_eq_zero_of_isUnit huf)
    fun hf0 => not_lt_of_gt hf <| hf0.symm ▸ (@degree_zero R _).symm ▸ WithBot.bot_lt_coe _

theorem exists_irreducible_of_natDegree_pos (hf : 0 < f.natDegree) : ∃ g, Irreducible g ∧ g ∣ f :=
  exists_irreducible_of_degree_pos <| by
    contrapose! hf
    exact natDegree_le_of_degree_le hf

-- DISSOLVED: exists_irreducible_of_natDegree_ne_zero

end Polynomial

section UniqueFactorizationDomain

variable (σ : Type v) {D : Type u} [CommRing D] [UniqueFactorizationMonoid D]

open UniqueFactorizationMonoid

namespace Polynomial

-- INSTANCE (free from Core): (priority
