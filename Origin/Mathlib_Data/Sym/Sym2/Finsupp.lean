/-
Extracted from Data/Sym/Sym2/Finsupp.lean
Genuine: 3 of 4 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-!
# Finitely supported functions from the symmetric square

This file lifts functions `α →₀ M₀` to functions `Sym2 α →₀ M₀` by precomposing with multiplication.
-/

open Sym2

variable {α M₀ : Type*} [CommMonoidWithZero M₀] {f : α →₀ M₀}

namespace Finsupp

lemma sym2_support_eq_preimage_support_mul [NoZeroDivisors M₀] (f : α →₀ M₀) :
    f.support.sym2 = map f ⁻¹' mul.support := by ext ⟨a, b⟩; simp

-- DISSOLVED: mem_sym2_support_of_mul_ne_zero

noncomputable def sym2Mul (f : α →₀ M₀) : Sym2 α →₀ M₀ :=
  .onFinset f.support.sym2 (fun p ↦ mul (p.map f)) mem_sym2_support_of_mul_ne_zero

lemma support_sym2Mul_subset : f.sym2Mul.support ⊆ f.support.sym2 := support_onFinset_subset
