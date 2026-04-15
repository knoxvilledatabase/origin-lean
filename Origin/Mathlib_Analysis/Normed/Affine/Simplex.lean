/-
Extracted from Analysis/Normed/Affine/Simplex.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Simplices in torsors over normed spaces.

This file defines properties of simplices in a `NormedAddTorsor`.

## Main definitions

* `Affine.Simplex.Scalene`
* `Affine.Simplex.Equilateral`
* `Affine.Simplex.Regular`

-/

namespace Affine

open Function

variable {R V P : Type*} [Ring R] [SeminormedAddCommGroup V] [PseudoMetricSpace P] [Module R V]

variable [NormedAddTorsor V P]

namespace Simplex

variable {m n : ℕ}

def Scalene (s : Simplex R P n) : Prop :=
  Injective fun i : {x : Fin (n + 1) × Fin (n + 1) // x.1 < x.2} ↦
    dist (s.points i.val.1) (s.points i.val.2)

lemma Scalene.dist_ne {s : Simplex R P n} (hs : s.Scalene) {i₁ i₂ i₃ i₄ : Fin (n + 1)}
    (h₁₂ : i₁ ≠ i₂) (h₃₄ : i₃ ≠ i₄) (h₁₂₃₄ : ¬(i₁ = i₃ ∧ i₂ = i₄)) (h₁₂₄₃ : ¬(i₁ = i₄ ∧ i₂ = i₃)) :
    dist (s.points i₁) (s.points i₂) ≠ dist (s.points i₃) (s.points i₄) := by
  rw [Classical.not_and_iff_not_or_not] at h₁₂₃₄ h₁₂₄₃
  rcases h₁₂.lt_or_gt with h₁₂lt | h₂₁lt <;> rcases h₃₄.lt_or_gt with h₃₄lt | h₄₃lt
  · apply hs.ne (a₁ := ⟨(i₁, i₂), h₁₂lt⟩) (a₂ := ⟨(i₃, i₄), h₃₄lt⟩)
    cases h₁₂₃₄ <;> simp [*]
  · nth_rw 2 [dist_comm]
    apply hs.ne (a₁ := ⟨(i₁, i₂), h₁₂lt⟩) (a₂ := ⟨(i₄, i₃), h₄₃lt⟩)
    cases h₁₂₄₃ <;> simp [*]
  · rw [dist_comm]
    apply hs.ne (a₁ := ⟨(i₂, i₁), h₂₁lt⟩) (a₂ := ⟨(i₃, i₄), h₃₄lt⟩)
    cases h₁₂₄₃ <;> simp [*]
  · rw [dist_comm]
    nth_rw 2 [dist_comm]
    apply hs.ne (a₁ := ⟨(i₂, i₁), h₂₁lt⟩) (a₂ := ⟨(i₄, i₃), h₄₃lt⟩)
    cases h₁₂₃₄ <;> simp [*]
