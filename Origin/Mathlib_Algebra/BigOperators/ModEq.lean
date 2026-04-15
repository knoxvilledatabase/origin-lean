/-
Extracted from Algebra/BigOperators/ModEq.lean
Genuine: 12 of 12 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Congruence modulo natural and integer numbers for big operators

In this file we prove various versions of the following theorem:
if `f i ≡ g i [MOD n]` for all `i ∈ s`, then `∏ i ∈ s, f i ≡ ∏ i ∈ s, g i [MOD n]`,
and similarly for sums.

We prove it for lists, multisets, and finsets, as well as for natural and integer numbers.
-/

namespace Nat

variable {α : Type*} {n : ℕ} {l : List α} {f g : α → ℕ}

namespace ModEq

theorem listProd_map (h : ∀ x ∈ l, f x ≡ g x [MOD n]) :
    (l.map f).prod ≡ (l.map g).prod [MOD n] := by
  induction l <;> aesop (add unsafe ModEq.mul)

theorem listProd_map_one (h : ∀ x ∈ l, f x ≡ 1 [MOD n]) : (l.map f).prod ≡ 1 [MOD n] :=
  (listProd_map h).trans <| by simp [ModEq.refl]

theorem listProd_one {l : List ℕ} (h : ∀ x ∈ l, x ≡ 1 [MOD n]) : l.prod ≡ 1 [MOD n] := by
  simpa using listProd_map_one h

theorem listSum_map (h : ∀ x ∈ l, f x ≡ g x [MOD n]) : (l.map f).sum ≡ (l.map g).sum [MOD n] := by
  induction l <;> aesop (add unsafe ModEq.add)

theorem listSum_map_zero (h : ∀ x ∈ l, f x ≡ 0 [MOD n]) : (l.map f).sum ≡ 0 [MOD n] := by
  simpa using listSum_map h

theorem listSum_zero {l : List ℕ} (h : ∀ x ∈ l, x ≡ 0 [MOD n]) : l.sum ≡ 0 [MOD n] := by
  simpa using listSum_map h

theorem multisetProd_map {s : Multiset α} (h : ∀ x ∈ s, f x ≡ g x [MOD n]) :
    (s.map f).prod ≡ (s.map g).prod [MOD n] := by
  rcases s with ⟨l⟩
  simpa using listProd_map (l := l) h

theorem multisetProd_map_one {s : Multiset α} (h : ∀ x ∈ s, f x ≡ 1 [MOD n]) :
    (s.map f).prod ≡ 1 [MOD n] := by
  simpa using multisetProd_map h

theorem multisetProd_one {s : Multiset ℕ} (h : ∀ x ∈ s, x ≡ 1 [MOD n]) : s.prod ≡ 1 [MOD n] := by
  simpa using multisetProd_map_one h

theorem multisetSum_map {s : Multiset α} (h : ∀ x ∈ s, f x ≡ g x [MOD n]) :
    (s.map f).sum ≡ (s.map g).sum [MOD n] := by
  rcases s with ⟨l⟩
  simpa using listSum_map (l := l) h

theorem multisetSum_map_zero {s : Multiset α} (h : ∀ x ∈ s, f x ≡ 0 [MOD n]) :
    (s.map f).sum ≡ 0 [MOD n] := by
  simpa using multisetSum_map h

theorem multisetSum_zero {s : Multiset ℕ} (h : ∀ x ∈ s, x ≡ 0 [MOD n]) : s.sum ≡ 0 [MOD n] := by
  simpa using multisetSum_map h
