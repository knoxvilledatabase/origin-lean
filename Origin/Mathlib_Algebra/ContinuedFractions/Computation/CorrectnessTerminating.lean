/-
Extracted from Algebra/ContinuedFractions/Computation/CorrectnessTerminating.lean
Genuine: 5 of 7 | Dissolved: 1 | Infrastructure: 1
-/
import Origin.Core

/-!
# Correctness of Terminating Continued Fraction Computations (`GenContFract.of`)

## Summary

We show the correctness of the algorithm computing continued fractions (`GenContFract.of`)
in case of termination in the following sense:

At every step `n : ℕ`, we can obtain the value `v` by adding a specific residual term to the last
denominator of the fraction described by `(GenContFract.of v).convs' n`.
The residual term will be zero exactly when the continued fraction terminated; otherwise, the
residual term will be given by the fractional part stored in `GenContFract.IntFractPair.stream v n`.

For an example, refer to
`GenContFract.compExactValue_correctness_of_stream_eq_some` and for more
information about the computation process, refer to `Algebra.ContinuedFractions.Computation.Basic`.

## Main definitions

- `GenContFract.compExactValue` can be used to compute the exact value approximated by the
  continued fraction `GenContFract.of v` by adding a residual term as described in the summary.

## Main Theorems

- `GenContFract.compExactValue_correctness_of_stream_eq_some` shows that
  `GenContFract.compExactValue` indeed returns the value `v` when given the convergent and
  fractional part as described in the summary.
- `GenContFract.of_correctness_of_terminatedAt` shows the equality
  `v = (GenContFract.of v).convs n` if `GenContFract.of v` terminated at position `n`.
-/

assert_not_exists Finset

namespace GenContFract

open GenContFract (of)

variable {K : Type*} [Field K] [LinearOrder K] {v : K} {n : ℕ}

protected def compExactValue (pconts conts : Pair K) (fr : K) : K :=
  -- if the fractional part is zero, we exactly approximated the value by the last continuants
  if fr = 0 then
    conts.a / conts.b
  else -- otherwise, we have to include the fractional part in a final continuants step.
    let exactConts := nextConts 1 fr⁻¹ pconts conts
    exactConts.a / exactConts.b

variable [FloorRing K]

-- DISSOLVED: compExactValue_correctness_of_stream_eq_some_aux_comp

open GenContFract

  (compExactValue compExactValue_correctness_of_stream_eq_some_aux_comp)

open GenContFract (of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none)

theorem of_correctness_of_nth_stream_eq_none (nth_stream_eq_none : IntFractPair.stream v n = none) :
    v = (of v).convs (n - 1) := by
  induction n with
  | zero => contradiction
  -- IntFractPair.stream v 0 ≠ none
  | succ n IH =>
    let g := of v
    change v = g.convs n
    obtain ⟨nth_stream_eq_none⟩ | ⟨ifp_n, nth_stream_eq, nth_stream_fr_eq_zero⟩ :
      IntFractPair.stream v n = none ∨ ∃ ifp, IntFractPair.stream v n = some ifp ∧ ifp.fr = 0 :=
      IntFractPair.succ_nth_stream_eq_none_iff.1 nth_stream_eq_none
    · cases n with
      | zero => contradiction
      | succ n' =>
        -- IntFractPair.stream v 0 ≠ none
        have : g.TerminatedAt n' :=
          of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none.2
            nth_stream_eq_none
        have : g.convs (n' + 1) = g.convs n' :=
          convs_stable_of_terminated n'.le_succ this
        rw [this]
        exact IH nth_stream_eq_none
    · simpa [nth_stream_fr_eq_zero, compExactValue] using
        compExactValue_correctness_of_stream_eq_some nth_stream_eq

theorem of_correctness_of_terminatedAt (terminatedAt_n : (of v).TerminatedAt n) :
    v = (of v).convs n :=
  have : IntFractPair.stream v (n + 1) = none :=
    of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none.1 terminatedAt_n
  of_correctness_of_nth_stream_eq_none this

theorem of_correctness_of_terminates (terminates : (of v).Terminates) :
    ∃ n : ℕ, v = (of v).convs n :=
  Exists.elim terminates fun n terminatedAt_n =>
    Exists.intro n (of_correctness_of_terminatedAt terminatedAt_n)

open Filter

theorem of_correctness_atTop_of_terminates (terminates : (of v).Terminates) :
    ∀ᶠ n in atTop, v = (of v).convs n := by
  rw [eventually_atTop]
  obtain ⟨n, terminatedAt_n⟩ : ∃ n, (of v).TerminatedAt n := terminates
  use n
  intro m m_geq_n
  rw [convs_stable_of_terminated m_geq_n terminatedAt_n]
  exact of_correctness_of_terminatedAt terminatedAt_n

end GenContFract
