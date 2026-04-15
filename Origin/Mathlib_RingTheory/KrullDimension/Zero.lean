/-
Extracted from RingTheory/KrullDimension/Zero.lean
Genuine: 7 of 7 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Zero-dimensional rings

We provide further API for zero-dimensional rings.
Basic definitions and lemmas are provided in `Mathlib/RingTheory/KrullDimension/Basic.lean`.

-/

section CommSemiring

variable {R : Type*} [CommSemiring R] [Ring.KrullDimLE 0 R] (I : Ideal R)

lemma Ring.KrullDimLE.mem_minimalPrimes_iff {I J : Ideal R} :
    I ∈ J.minimalPrimes ↔ I.IsPrime ∧ J ≤ I :=
  ⟨fun H ↦ H.1, fun H ↦ ⟨H, fun _ h e ↦ (h.1.isMaximal'.eq_of_le H.1.ne_top e).ge⟩⟩

lemma Ring.KrullDimLE.mem_minimalPrimes_iff_le_of_isPrime {I J : Ideal R} [I.IsPrime] :
    I ∈ J.minimalPrimes ↔ J ≤ I := by
  rwa [mem_minimalPrimes_iff, and_iff_right]

variable (R) in

lemma Ring.KrullDimLE.minimalPrimes_eq_setOf_isPrime :
    minimalPrimes R = { I | I.IsPrime } := by
  ext; simp [minimalPrimes, mem_minimalPrimes_iff]

variable (R) in

lemma Ring.KrullDimLE.minimalPrimes_eq_setOf_isMaximal :
    minimalPrimes R = { I | I.IsMaximal } := by
  ext; simp [minimalPrimes_eq_setOf_isPrime, Ideal.isMaximal_iff_isPrime]

example [Subsingleton R] : Ring.KrullDimLE 0 R := inferInstance

lemma Ring.KrullDimLE.isField_of_isDomain [IsDomain R] : IsField R := by
  by_contra h
  obtain ⟨p, hp, h⟩ := Ring.not_isField_iff_exists_prime.mp h
  exact hp.symm (Ideal.isPrime_bot.isMaximal'.eq_of_le h.ne_top bot_le)

omit [Ring.KrullDimLE 0 R] in

lemma ringKrullDimZero_iff_ringKrullDim_eq_zero [Nontrivial R] :
    Ring.KrullDimLE 0 R ↔ ringKrullDim R = 0 := by
  rw [Ring.KrullDimLE, Order.krullDimLE_iff, le_antisymm_iff, ← ringKrullDim, Nat.cast_zero,
    iff_self_and]
  exact fun _ ↦ ringKrullDim_nonneg_of_nontrivial

section IsLocalRing

omit [Ring.KrullDimLE 0 R] in

variable (R) in

lemma Ring.krullDimLE_zero_and_isLocalRing_tfae :
    List.TFAE
    [ Ring.KrullDimLE 0 R ∧ IsLocalRing R,
      ∃! I : Ideal R, I.IsPrime,
      ∀ x : R, IsNilpotent x ↔ ¬ IsUnit x,
      (nilradical R).IsMaximal ] := by
  tfae_have 1 → 3 := by
    intro ⟨h₁, h₂⟩ x
    change x ∈ nilradical R ↔ x ∈ IsLocalRing.maximalIdeal R
    rw [nilradical, Ideal.radical_eq_sInf]
    simp [← Ideal.isMaximal_iff_isPrime, IsLocalRing.isMaximal_iff]
  tfae_have 3 → 4 := by
    refine fun H ↦ ⟨fun e ↦ ?_, fun I hI ↦ ?_⟩
    · obtain ⟨n, hn⟩ := (Ideal.eq_top_iff_one _).mp e
      exact (H 0).mp .zero ((show (1 : R) = 0 by simpa using hn) ▸ isUnit_one)
    · obtain ⟨x, hx, hx'⟩ := (SetLike.lt_iff_le_and_exists.mp hI).2
      exact Ideal.eq_top_of_isUnit_mem _ hx (not_not.mp ((H x).not.mp hx'))
  tfae_have 4 → 2 := fun H ↦ ⟨_, H.isPrime, fun p (hp : p.IsPrime) ↦
      (H.eq_of_le hp.ne_top (nilradical_le_prime p)).symm⟩
  tfae_have 2 → 1 := by
    rintro ⟨P, hP₁, hP₂⟩
    obtain ⟨P, hP₃, -⟩ := P.exists_le_maximal hP₁.ne_top
    obtain rfl := hP₂ P hP₃.isPrime
    exact ⟨.mk₀ fun Q h ↦ hP₂ Q h ▸ hP₃, .of_unique_max_ideal ⟨P, hP₃, fun Q h ↦ hP₂ Q h.isPrime⟩⟩
  tfae_finish
