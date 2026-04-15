/-
Extracted from Algebra/BigOperators/Ring/Finset.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Results about big operators with values in a (semi)ring

We prove results about big operators that involve some interaction between
multiplicative and additive structures on the values being combined.
-/

assert_not_exists Field

open Fintype

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

namespace Finset

lemma prod_neg [CommMonoid M] [HasDistribNeg M] (f : ι → M) :
    ∏ x ∈ s, -f x = (-1) ^ #s * ∏ x ∈ s, f x := by
  simpa using (s.1.map f).prod_map_neg

section AddCommMonoidWithOne

variable [AddCommMonoidWithOne R]

lemma natCast_card_filter (p) [DecidablePred p] (s : Finset ι) :
    (#{x ∈ s | p x} : R) = ∑ a ∈ s, if p a then (1 : R) else 0 := by
  rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_one]
