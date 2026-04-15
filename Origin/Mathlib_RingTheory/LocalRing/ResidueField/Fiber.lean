/-
Extracted from RingTheory/LocalRing/ResidueField/Fiber.lean
Genuine: 3 of 5 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# The fiber of a ring homomorphism at a prime ideal

## Main results

* `Ideal.Fiber`: `p.Fiber S` is the fiber of a prime `p` of `R` in an `R`-algebra `S`,
  defined to be `κ(p) ⊗ S`.
* `PrimeSpectrum.preimageHomeomorphFiber` : We show that there is a homeomorphism between the
  fiber of the induced map `PrimeSpectrum S → PrimeSpectrum R` at a prime ideal `p` and
  the prime spectrum of `p.Fiber S`.
-/

open Algebra TensorProduct nonZeroDivisors

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime]

set_option backward.isDefEq.respectTransparency false in

open IsLocalRing in

-- INSTANCE (free from Core): [IsLocalRing

lemma Ideal.ResidueField.exists_smul_eq_tmul_one
    (x : S ⊗[R] p.ResidueField) : ∃ r ∉ p, ∃ s, r • x = s ⊗ₜ[R] 1 := by
  obtain ⟨t, r, a, hrt, e⟩ := RingHom.SurjectiveOnStalks.exists_mul_eq_tmul
    p.surjectiveOnStalks_residueField x ⊥ isPrime_bot
  obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective t
  obtain ⟨⟨y, t⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl t
  simp only [smul_def, Submodule.mem_bot, mul_eq_zero, algebraMap_residueField_eq_zero,
    IsLocalRing.residue_eq_zero_iff, not_or, IsLocalization.AtPrime.mk'_mem_maximal_iff] at hrt
  refine ⟨r * y, p.primeCompl.mul_mem hrt.1 hrt.2, y • a, ?_⟩
  rw [Algebra.smul_def, ← Algebra.TensorProduct.includeRight.commutes, smul_tmul,
    ← Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.includeRight_apply]
  simpa [← tmul_smul, Submonoid.smul_def, ← smul_mul_assoc, smul_comm _ r,
    ← IsLocalRing.ResidueField.algebraMap_eq, ← algebraMap.coe_smul,
    ← IsScalarTower.algebraMap_apply] using congr(t • $e)

abbrev Ideal.Fiber (p : Ideal R) [p.IsPrime] (S : Type*) [CommRing S] [Algebra R S] : Type _ :=
  p.ResidueField ⊗[R] S

-- INSTANCE (free from Core): (p

lemma Ideal.Fiber.exists_smul_eq_one_tmul (x : p.Fiber S) : ∃ r ∉ p, ∃ s, r • x = 1 ⊗ₜ[R] s := by
  obtain ⟨r, hr, s, e⟩ := Ideal.ResidueField.exists_smul_eq_tmul_one _
    (Algebra.TensorProduct.comm _ _ _ x)
  refine ⟨r, hr, s, by simpa using congr((Algebra.TensorProduct.comm _ _ _).symm $e)⟩

set_option backward.isDefEq.respectTransparency false in

variable (R S) in
