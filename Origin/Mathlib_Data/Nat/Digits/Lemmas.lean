/-
Extracted from Data/Nat/Digits/Lemmas.lean
Genuine: 2 of 3 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-!
# Digits of a natural number

This provides lemma about the digits of natural numbers.
-/

namespace Nat

variable {n : ℕ}

theorem ofDigits_eq_sum_mapIdx_aux (b : ℕ) (l : List ℕ) :
    (l.zipWith ((fun a i : ℕ => a * b ^ (i + 1))) (List.range l.length)).sum =
      b * (l.zipWith (fun a i => a * b ^ i) (List.range l.length)).sum := by
  suffices
    l.zipWith (fun a i : ℕ => a * b ^ (i + 1)) (List.range l.length) =
      l.zipWith (fun a i => b * (a * b ^ i)) (List.range l.length)
    by simp [this]
  congr; ext; ring

theorem ofDigits_eq_sum_mapIdx (b : ℕ) (L : List ℕ) :
    ofDigits b L = (L.mapIdx fun i a => a * b ^ i).sum := by
  rw [List.mapIdx_eq_zipIdx_map, List.zipIdx_eq_zip_range', List.map_zip_eq_zipWith,
    ofDigits_eq_foldr, ← List.range_eq_range']
  induction L with
  | nil => simp
  | cons hd tl hl =>
    simpa [List.range_succ_eq_map, List.zipWith_map_right, ofDigits_eq_sum_mapIdx_aux] using
      Or.inl hl

/-!
### Properties

This section contains various lemmas of properties relating to `digits` and `ofDigits`.
-/

-- DISSOLVED: length_digits
