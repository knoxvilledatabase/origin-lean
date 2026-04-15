/-
Extracted from Algebra/BigOperators/Field.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Results about big operators with values in a field
-/

open Fintype

variable {ι K : Type*} [DivisionSemiring K]

lemma Multiset.sum_map_div (s : Multiset ι) (f : ι → K) (a : K) :
    (s.map (fun x ↦ f x / a)).sum = (s.map f).sum / a := by
  simp only [div_eq_mul_inv, Multiset.sum_map_mul_right]

lemma Finset.sum_div (s : Finset ι) (f : ι → K) (a : K) :
    (∑ i ∈ s, f i) / a = ∑ i ∈ s, f i / a := by simp only [div_eq_mul_inv, sum_mul]

namespace Finset

variable {α β : Type*} [Fintype β]
