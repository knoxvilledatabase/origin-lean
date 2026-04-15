/-
Extracted from RingTheory/KrullDimension/NonZeroDivisors.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Krull dimension and non-zero-divisors

## Main results
- `ringKrullDim_quotient_succ_le_of_nonZeroDivisor`: If `r` is not a zero divisor, then
  `dim R/r + 1 ≤ dim R`.
- `ringKrullDim_succ_le_ringKrullDim_polynomial`: `dim R + 1 ≤ dim R[X]`.
- `ringKrullDim_add_enatCard_le_ringKrullDim_mvPolynomial`: `dim R + #σ ≤ dim R[σ]`.
-/

open scoped nonZeroDivisors

variable {R S : Type*} [CommRing R] [CommRing S]

lemma ringKrullDim_quotient (I : Ideal R) :
    ringKrullDim (R ⧸ I) = Order.krullDim (PrimeSpectrum.zeroLocus (R := R) I) := by
  rw [ringKrullDim, Order.krullDim_eq_of_orderIso I.primeSpectrumQuotientOrderIsoZeroLocus]

lemma ringKrullDim_quotient_succ_le_of_nonZeroDivisor
    {r : R} (hr : r ∈ R⁰) :
    ringKrullDim (R ⧸ Ideal.span {r}) + 1 ≤ ringKrullDim R := by
  by_cases hr' : Ideal.span {r} = ⊤
  · rw [hr', ringKrullDim_eq_bot_of_subsingleton]
    simp
  have : Nonempty (PrimeSpectrum.zeroLocus (R := R) (Ideal.span {r})) := by
    rwa [Set.nonempty_coe_sort, Set.nonempty_iff_ne_empty, ne_eq,
      PrimeSpectrum.zeroLocus_empty_iff_eq_top]
  have := Ideal.Quotient.nontrivial_iff.mpr hr'
  have := (Ideal.Quotient.mk (Ideal.span {r})).domain_nontrivial
  rw [ringKrullDim_quotient, Order.krullDim_eq_iSup_length, ringKrullDim,
    Order.krullDim_eq_iSup_length, ← WithBot.coe_one, ← WithBot.coe_add,
    ENat.iSup_add, WithBot.coe_le_coe, iSup_le_iff]
  intro l
  obtain ⟨p, hp, hp'⟩ := Ideal.exists_minimalPrimes_le (J := l.head.1.asIdeal) bot_le
  let p' : PrimeSpectrum R := ⟨p, hp.1.1⟩
  have hp' : p' < l.head := lt_of_le_of_ne hp' fun h ↦ Set.disjoint_iff.mp
    (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hp)
    ⟨show r ∈ p by simpa [← h] using l.head.2, hr⟩
  refine le_trans ?_ (le_iSup _ ((l.map Subtype.val (fun _ _ ↦ id)).cons p' hp'))
  simp

lemma ringKrullDim_succ_le_of_surjective (f : R →+* S) (hf : Function.Surjective f)
    {r : R} (hr : r ∈ R⁰) (hr' : f r = 0) : ringKrullDim S + 1 ≤ ringKrullDim R := by
  refine le_trans ?_ (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr)
  gcongr
  exact ringKrullDim_le_of_surjective (Ideal.Quotient.lift _ f (RingHom.ker f
    |>.span_singleton_le_iff_mem.mpr hr')) (Ideal.Quotient.lift_surjective_of_surjective _ _ hf)

open Polynomial in

lemma ringKrullDim_succ_le_ringKrullDim_polynomial :
    ringKrullDim R + 1 ≤ ringKrullDim R[X] :=
  ringKrullDim_succ_le_of_surjective constantCoeff (⟨C ·, coeff_C_zero⟩)
    X_mem_nonzeroDivisors coeff_X_zero

open MvPolynomial in
