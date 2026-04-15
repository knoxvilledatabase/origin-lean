/-
Extracted from RingTheory/Ideal/MinimalPrime/Localization.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Minimal primes and localization

We provide various results concerning the minimal primes above an ideal that require the theory
of localizations.

## Main results
- `Ideal.exists_minimalPrimes_comap_eq` If `p` is a minimal prime over `f ⁻¹ I`, then it is the
  preimage of some minimal prime over `I`.
- `Ideal.minimalPrimes_eq_comap`: The minimal primes over `I` are precisely the preimages of
  minimal primes of `R ⧸ I`.
- `IsLocalization.minimalPrimes_comap`: If `A` is a localization of `R` with respect to the
  submonoid `S`, `J` is an ideal of `A`, then the minimal primes over the preimage of `J`
  (under `R →+* A`) are exactly the preimages of the minimal primes over `J`.
- `IsLocalization.minimalPrimes_map`: If `A` is a localization of `R` with respect to the
  submonoid `S`, `J` is an ideal of `R`, then the minimal primes over the span of the image of `J`
  (under `R →+* A`) are exactly the ideals of `A` such that the preimage of which is a minimal prime
  over `J`.
- `Localization.AtPrime.prime_unique_of_minimal`: When localizing at a minimal prime ideal `I`,
  the resulting ring only has a single prime ideal.
-/

variable {R S : Type*} [CommSemiring R] [CommSemiring S] {I J : Ideal R}

theorem Ideal.iUnion_minimalPrimes :
    ⋃ p ∈ I.minimalPrimes, p = { x | ∃ y ∉ I.radical, x * y ∈ I.radical } := by
  classical
  ext x
  simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop, Set.mem_setOf_eq]
  constructor
  · rintro ⟨p, ⟨⟨hp₁, hp₂⟩, hp₃⟩, hxp⟩
    have : p.map (algebraMap R (Localization.AtPrime p)) ≤ (I.map (algebraMap _ _)).radical := by
      rw [Ideal.radical_eq_sInf, le_sInf_iff]
      rintro q ⟨hq', hq⟩
      obtain ⟨h₁, h₂⟩ := ((IsLocalization.AtPrime.orderIsoOfPrime _ p) ⟨q, hq⟩).2
      rw [Ideal.map_le_iff_le_comap] at hq' ⊢
      exact hp₃ ⟨h₁, hq'⟩ h₂
    obtain ⟨n, hn⟩ := this (Ideal.mem_map_of_mem _ hxp)
    rw [IsLocalization.mem_map_algebraMap_iff (M := p.primeCompl)] at hn
    obtain ⟨⟨a, b⟩, hn⟩ := hn
    rw [← map_pow, ← map_mul, IsLocalization.eq_iff_exists p.primeCompl] at hn
    obtain ⟨t, ht⟩ := hn
    refine ⟨t * b, fun h ↦ (t * b).2 (hp₁.radical_le_iff.mpr hp₂ h), n + 1, ?_⟩
    simp only at ht
    have : (x * (t.1 * b.1)) ^ (n + 1) = (t.1 ^ n * b.1 ^ n * x * t.1) * a := by
      rw [mul_assoc, ← ht]; ring
    rw [this]
    exact I.mul_mem_left _ a.2
  · rintro ⟨y, hy, hx⟩
    obtain ⟨p, hp, hyp⟩ : ∃ p ∈ I.minimalPrimes, y ∉ p := by
      simpa [← Ideal.sInf_minimalPrimes] using hy
    refine ⟨p, hp, (hp.1.1.mem_or_mem ?_).resolve_right hyp⟩
    exact hp.1.1.radical_le_iff.mpr hp.1.2 hx

theorem Ideal.exists_mul_mem_of_mem_minimalPrimes
    {p : Ideal R} (hp : p ∈ I.minimalPrimes) {x : R} (hx : x ∈ p) :
    ∃ y ∉ I, x * y ∈ I := by
  classical
  obtain ⟨y, hy, n, hx⟩ := Ideal.iUnion_minimalPrimes.subset (Set.mem_biUnion hp hx)
  have H : ∃ m, x ^ m * y ^ n ∈ I := ⟨n, mul_pow x y n ▸ hx⟩
  have : Nat.find H ≠ 0 :=
    fun h ↦ hy ⟨n, by simpa only [h, pow_zero, one_mul] using Nat.find_spec H⟩
  refine ⟨x ^ (Nat.find H - 1) * y ^ n, Nat.find_min H (Nat.sub_one_lt this), ?_⟩
  rw [← mul_assoc, ← pow_succ', tsub_add_cancel_of_le (Nat.one_le_iff_ne_zero.mpr this)]
  exact Nat.find_spec H

theorem IsSMulRegular.notMem_of_mem_minimalPrimes
    {M : Type*} [AddCommMonoid M] [Module R M] {x : R} (reg : IsSMulRegular M x)
    {p : Ideal R} (hp : p ∈ (Module.annihilator R M).minimalPrimes) : x ∉ p := by
  intro hx
  rcases Ideal.exists_mul_mem_of_mem_minimalPrimes hp hx with ⟨y, hy, hxy⟩
  rcases not_forall.mp (Module.mem_annihilator.not.mp hy) with ⟨m, hm⟩
  exact hm (reg.right_eq_zero_of_smul ((smul_smul x y m).trans (Module.mem_annihilator.mp hxy m)))

lemma Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes {p : Ideal R} (hp : p ∈ minimalPrimes R) :
    Disjoint (p : Set R) (nonZeroDivisors R) := by
  simp_rw [Set.disjoint_left, SetLike.mem_coe, mem_nonZeroDivisors_iff_right, not_forall,
    exists_prop, @and_comm (_ * _ = _), ← mul_comm]
  exact fun _ ↦ Ideal.exists_mul_mem_of_mem_minimalPrimes hp

theorem Ideal.exists_comap_eq_of_mem_minimalPrimes {I : Ideal S} (f : R →+* S) (p)
    (H : p ∈ (I.comap f).minimalPrimes) : ∃ p' : Ideal S, p'.IsPrime ∧ I ≤ p' ∧ p'.comap f = p :=
  have := H.1.1
  have ⟨p', hIp', hp', le⟩ := exists_ideal_comap_le_prime p I H.1.2
  ⟨p', hp', hIp', le.antisymm (H.2 ⟨inferInstance, comap_mono hIp'⟩ le)⟩
