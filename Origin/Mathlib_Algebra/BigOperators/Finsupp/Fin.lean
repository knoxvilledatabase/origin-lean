/-
Extracted from Algebra/BigOperators/Finsupp/Fin.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# `Finsupp.sum` and `Finsupp.prod` over `Fin`

This file contains theorems relevant to big operators on finitely supported functions over `Fin`.
-/

variable {M N : Type*}

namespace Finsupp

lemma sum_cons [AddCommMonoid M] (n : ℕ) (σ : Fin n →₀ M) (i : M) :
    (sum (cons i σ) fun _ e ↦ e) = i + sum σ (fun _ e ↦ e) := by
  rw [sum_fintype _ _ (fun _ => rfl), sum_fintype _ _ (fun _ => rfl)]
  exact Fin.sum_cons i σ

lemma sum_cons' [Zero M] [AddCommMonoid N] (n : ℕ) (σ : Fin n →₀ M) (i : M)
    (f : Fin (n + 1) → M → N) (h : ∀ x, f x 0 = 0) :
    (sum (Finsupp.cons i σ) f) = f 0 i + sum σ (Fin.tail f) := by
  rw [sum_fintype _ _ (fun _ => by apply h), sum_fintype _ _ (fun _ => by apply h)]
  simp_rw [Fin.sum_univ_succ, cons_zero, cons_succ]
  congr

theorem ofSupportFinite_fin_two_eq (n : Fin 2 →₀ ℕ) :
    ofSupportFinite ![n 0, n 1] (Set.toFinite _) = n := by
  rw [Finsupp.ext_iff, Fin.forall_fin_two]
  exact ⟨rfl, rfl⟩

end Finsupp

section Fin2

variable (M) in
