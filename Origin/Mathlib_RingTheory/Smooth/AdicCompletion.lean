/-
Extracted from RingTheory/Smooth/AdicCompletion.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Formally smooth algebras and adic completion

Let `A` be a formally smooth `R`-algebra. Then any algebra map
`A →ₐ[R] S ⧸ I` lifts to an algebra map `A →ₐ[R] S` if `S` is `I`-adically complete.

This is used in the proof that a smooth algebra over a Noetherian ring is flat
(see `Mathlib.RingTheory.Smooth.Flat`).
-/

universe u v

namespace Algebra.FormallySmooth

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  {S : Type*} [CommRing S] [Algebra R S] (I : Ideal S) (f : A →ₐ[R] S ⧸ I)

open RingHom

variable [FormallySmooth R A]

noncomputable def liftAdicCompletionAux : (m : ℕ) → A →ₐ[R] S ⧸ (I ^ m)
  | 0 =>
    haveI : Subsingleton (S ⧸ I ^ 0) := by simp
    default
  | 1 => (Ideal.quotientEquivAlgOfEq R (show I = I ^ 1 by simp)).toAlgHom.comp f
  | m + 2 =>
    letI T := S ⧸ I ^ (m + 1 + 1)
    letI J : Ideal T := (I ^ (m + 1)).map (Ideal.Quotient.mkₐ R (I ^ (m + 1 + 1)))
    letI q : A →ₐ[R] T ⧸ J :=
      (DoubleQuot.quotQuotEquivQuotOfLEₐ R
        (Ideal.pow_le_pow_right (I := I) (m + 1).le_succ)).symm.toAlgHom.comp
      (liftAdicCompletionAux (m + 1))
    haveI : J ^ (m + 1 + 1) = 0 := by
      rw [← Ideal.map_pow, Submodule.zero_eq_bot, ← pow_mul]
      exact eq_bot_mono (Ideal.map_mono <| Ideal.pow_le_pow_right (by simp))
        (Ideal.map_quotient_self _)
    FormallySmooth.lift J ⟨m + 1 + 1, this⟩ q
