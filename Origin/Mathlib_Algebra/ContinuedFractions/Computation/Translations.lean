/-
Extracted from Algebra/ContinuedFractions/Computation/Translations.lean
Genuine: 4 of 8 | Dissolved: 3 | Infrastructure: 1
-/
import Origin.Core

/-!
# Basic Translation Lemmas Between Structures Defined for Computing Continued Fractions

## Summary

This is a collection of simple lemmas between the different structures used for the computation
of continued fractions defined in `Mathlib/Algebra/ContinuedFractions/Computation/Basic.lean`.
The file consists of three sections:
1. Recurrences and inversion lemmas for `IntFractPair.stream`: these lemmas give us inversion
   rules and recurrences for the computation of the stream of integer and fractional parts of
   a value.
2. Translation lemmas for the head term: these lemmas show us that the head term of the computed
   continued fraction of a value `v` is `⌊v⌋` and how this head term is moved along the structures
   used in the computation process.
3. Translation lemmas for the sequence: these lemmas show how the sequences of the involved
   structures (`IntFractPair.stream`, `IntFractPair.seq1`, and `GenContFract.of`) are connected,
   i.e. how the values are moved along the structures and the termination of one sequence implies
   the termination of another sequence.

## Main Theorems

- `succ_nth_stream_eq_some_iff` gives a recurrence to compute the `n + 1`th value of the sequence
  of integer and fractional parts of a value in case of non-termination.
- `succ_nth_stream_eq_none_iff` gives a recurrence to compute the `n + 1`th value of the sequence
  of integer and fractional parts of a value in case of termination.
- `get?_of_eq_some_of_succ_get?_intFractPair_stream` and
  `get?_of_eq_some_of_get?_intFractPair_stream_fr_ne_zero` show how the entries of the sequence
  of the computed continued fraction can be obtained from the stream of integer and fractional
  parts.
-/

assert_not_exists Finset

namespace GenContFract

open GenContFract (of)

variable {K : Type*} [DivisionRing K] [LinearOrder K] [FloorRing K] {v : K}

namespace IntFractPair

/-!
### Recurrences and Inversion Lemmas for `IntFractPair.stream`

Here we state some lemmas that give us inversion rules and recurrences for the computation of the
stream of integer and fractional parts of a value.
-/

variable {n : ℕ}

theorem stream_eq_none_of_fr_eq_zero {ifp_n : IntFractPair K}
    (stream_nth_eq : IntFractPair.stream v n = some ifp_n) (nth_fr_eq_zero : ifp_n.fr = 0) :
    IntFractPair.stream v (n + 1) = none := by
  obtain ⟨_, fr⟩ := ifp_n
  change fr = 0 at nth_fr_eq_zero
  simp [IntFractPair.stream, stream_nth_eq, nth_fr_eq_zero]

theorem succ_nth_stream_eq_none_iff :
    IntFractPair.stream v (n + 1) = none ↔
      IntFractPair.stream v n = none ∨ ∃ ifp, IntFractPair.stream v n = some ifp ∧ ifp.fr = 0 := by
  rw [IntFractPair.stream]
  cases IntFractPair.stream v n <;> simp [imp_false]

-- DISSOLVED: succ_nth_stream_eq_some_iff

-- DISSOLVED: stream_succ_of_some

theorem stream_succ_of_int [IsStrictOrderedRing K] (a : ℤ) (n : ℕ) :
    IntFractPair.stream (a : K) (n + 1) = none := by
  induction n with
  | zero =>
    refine IntFractPair.stream_eq_none_of_fr_eq_zero (IntFractPair.stream_zero (a : K)) ?_
    simp only [IntFractPair.of, Int.fract_intCast]
  | succ n ih => exact IntFractPair.succ_nth_stream_eq_none_iff.mpr (Or.inl ih)

theorem exists_succ_nth_stream_of_fr_zero {ifp_succ_n : IntFractPair K}
    (stream_succ_nth_eq : IntFractPair.stream v (n + 1) = some ifp_succ_n)
    (succ_nth_fr_eq_zero : ifp_succ_n.fr = 0) :
    ∃ ifp_n : IntFractPair K, IntFractPair.stream v n = some ifp_n ∧ ifp_n.fr⁻¹ = ⌊ifp_n.fr⁻¹⌋ := by
  -- get the witness from `succ_nth_stream_eq_some_iff` and prove that it has the additional
  -- properties
  rcases succ_nth_stream_eq_some_iff.mp stream_succ_nth_eq with
    ⟨ifp_n, seq_nth_eq, _, rfl⟩
  refine ⟨ifp_n, seq_nth_eq, ?_⟩
  simpa only [IntFractPair.of, Int.fract, sub_eq_zero] using succ_nth_fr_eq_zero

-- DISSOLVED: stream_succ

end IntFractPair

section Head

/-!
### Translation of the Head Term

Here we state some lemmas that show us that the head term of the computed continued fraction of a
value `v` is `⌊v⌋` and how this head term is moved along the structures used in the computation
process.
-/
