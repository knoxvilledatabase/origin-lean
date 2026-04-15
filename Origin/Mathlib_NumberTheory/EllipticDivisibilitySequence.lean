/-
Extracted from NumberTheory/EllipticDivisibilitySequence.lean
Genuine: 10 of 10 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Elliptic divisibility sequences

This file defines the type of an elliptic divisibility sequence (EDS) and a few examples.

## Mathematical background

Let `R` be a commutative ring. An elliptic sequence is a sequence `W : ℤ → R` satisfying
`W(m + n)W(m - n)W(r)² = W(m + r)W(m - r)W(n)² - W(n + r)W(n - r)W(m)²` for any `m, n, r ∈ ℤ`.
A divisibility sequence is a sequence `W : ℤ → R` satisfying `W(m) ∣ W(n)` for any `m, n ∈ ℤ` such
that `m ∣ n`. An elliptic divisibility sequence is simply a divisibility sequence that is elliptic.

Some examples of EDSs include
* the identity sequence,
* certain terms of Lucas sequences, and
* division polynomials of elliptic curves.

## Main definitions

* `IsEllSequence`: a sequence indexed by integers is an elliptic sequence.
* `IsDivSequence`: a sequence indexed by integers is a divisibility sequence.
* `IsEllDivSequence`: a sequence indexed by integers is an EDS.
* `preNormEDS'`: the auxiliary sequence for a normalised EDS indexed by `ℕ`.
* `preNormEDS`: the auxiliary sequence for a normalised EDS indexed by `ℤ`.
* `complEDS₂`: the 2-complement sequence for a normalised EDS indexed by `ℕ`.
* `normEDS`: the canonical example of a normalised EDS indexed by `ℤ`.
* `complEDS'`: the complement sequence for a normalised EDS indexed by `ℕ`.
* `complEDS`: the complement sequence for a normalised EDS indexed by `ℤ`.

## Main statements

* TODO: prove that `normEDS` satisfies `IsEllDivSequence`.
* TODO: prove that a normalised sequence satisfying `IsEllDivSequence` can be given by `normEDS`.

## Implementation notes

The normalised EDS `normEDS b c d n` is defined in terms of the auxiliary sequence
`preNormEDS (b ^ 4) c d n`, which are equal when `n` is odd, and which differ by a factor of `b`
when `n` is even. This coincides with the definition in the references since both agree for
`normEDS b c d 2` and for `normEDS b c d 4`, and the correct factors of `b` are removed in
`normEDS b c d (2 * (m + 2) + 1)` and in `normEDS b c d (2 * (m + 3))`.

One reason is to avoid the necessity for ring division by `b` in the inductive definition of
`normEDS b c d (2 * (m + 3))`. The idea is that it can be shown that `normEDS b c d (2 * (m + 3))`
always contains a factor of `b`, so it is possible to remove a factor of `b` *a posteriori*, but
stating this lemma requires first defining `normEDS b c d (2 * (m + 3))`, which requires having this
factor of `b` *a priori*. Another reason is to allow the definition of univariate `n`-division
polynomials of elliptic curves, omitting a factor of the bivariate `2`-division polynomial.

## References

M Ward, *Memoir on Elliptic Divisibility Sequences*

## Tags

elliptic, divisibility, sequence
-/

universe u v

variable {R : Type u} [CommRing R]

section IsEllDivSequence

variable (W : ℤ → R)

def IsEllSequence : Prop :=
  ∀ m n r : ℤ, W (m + n) * W (m - n) * W r ^ 2 =
    W (m + r) * W (m - r) * W n ^ 2 - W (n + r) * W (n - r) * W m ^ 2

def IsDivSequence : Prop :=
  ∀ m n : ℕ, m ∣ n → W m ∣ W n

def IsEllDivSequence : Prop :=
  IsEllSequence W ∧ IsDivSequence W

lemma isEllSequence_id : IsEllSequence id :=
  fun _ _ _ => by simp_rw [id_eq]; ring1

lemma isDivSequence_id : IsDivSequence id :=
  fun _ _ => Int.ofNat_dvd.mpr

theorem isEllDivSequence_id : IsEllDivSequence id :=
  ⟨isEllSequence_id, isDivSequence_id⟩

variable {W}

lemma IsEllSequence.smul (h : IsEllSequence W) (x : R) : IsEllSequence (x • W) :=
  fun m n r => by
    linear_combination (norm := (simp_rw [Pi.smul_apply, smul_eq_mul]; ring1)) x ^ 4 * h m n r

lemma IsDivSequence.smul (h : IsDivSequence W) (x : R) : IsDivSequence (x • W) :=
  fun m n r => mul_dvd_mul_left x <| h m n r

lemma IsEllDivSequence.smul (h : IsEllDivSequence W) (x : R) : IsEllDivSequence (x • W) :=
  ⟨h.left.smul x, h.right.smul x⟩

end IsEllDivSequence

variable (b c d : R)

section PreNormEDS

def preNormEDS' : ℕ → R
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => c
  | 4 => d
  | (n + 5) => let m := n / 2
    if hn : Even n then
      preNormEDS' (m + 4) * preNormEDS' (m + 2) ^ 3 * (if Even m then b else 1) -
        preNormEDS' (m + 1) * preNormEDS' (m + 3) ^ 3 * (if Even m then 1 else b)
    else
      have : m + 5 < n + 5 := by
        gcongr; exact Nat.div_lt_self (Nat.not_even_iff_odd.mp hn).pos one_lt_two
      preNormEDS' (m + 2) ^ 2 * preNormEDS' (m + 3) * preNormEDS' (m + 5) -
        preNormEDS' (m + 1) * preNormEDS' (m + 3) * preNormEDS' (m + 4) ^ 2
