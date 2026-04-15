/-
Extracted from Data/Finset/NatAntidiagonal.lean
Genuine: 3 of 5 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Antidiagonals in ℕ × ℕ as finsets

This file defines the antidiagonals of ℕ × ℕ as finsets: the `n`-th antidiagonal is the finset of
pairs `(i, j)` such that `i + j = n`. This is useful for polynomial multiplication and more
generally for sums going from `0` to `n`.

## Notes

This refines files `Data.List.NatAntidiagonal` and `Data.Multiset.NatAntidiagonal`, providing an
instance enabling `Finset.antidiagonal` on `Nat`.
-/

assert_not_exists Field

open Function

namespace Finset

namespace Nat

-- INSTANCE (free from Core): instHasAntidiagonal

lemma antidiagonal_eq_map' (n : ℕ) :
    antidiagonal n =
      (range (n + 1)).map ⟨fun i ↦ (n - i, i), fun _ _ h ↦ (Prod.ext_iff.1 h).2⟩ := by
  rw [← map_swap_antidiagonal, antidiagonal_eq_map, map_map]; rfl

lemma antidiagonal_eq_image (n : ℕ) :
    antidiagonal n = (range (n + 1)).image fun i ↦ (i, n - i) := by
  simp only [antidiagonal_eq_map, map_eq_image, Function.Embedding.coeFn_mk]

lemma antidiagonal_eq_image' (n : ℕ) :
    antidiagonal n = (range (n + 1)).image fun i ↦ (n - i, i) := by
  simp only [antidiagonal_eq_map', map_eq_image, Function.Embedding.coeFn_mk]
