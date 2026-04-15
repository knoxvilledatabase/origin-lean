/-
Extracted from RingTheory/Ideal/MinimalPrime/Colon.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Minimal primes over a colon ideal

We prove that a minimal prime over an ideal of the form `N.colon {x}` in a Noetherian ring is
itself an ideal of the form `N.colon {x'}`.

-/

namespace Submodule

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] {N : Submodule R M}
  {I : Ideal R} {x : M}

theorem exists_eq_colon_of_mem_minimalPrimes [IsNoetherianRing R]
    (hI : I ∈ (N.colon {x}).minimalPrimes) : ∃ x' : M, I = N.colon {x'} := by
  by_cases hx : x ∈ N
  · simp [show (colon N {x}) = ⊤ by simpa, Ideal.minimalPrimes_top] at hI
  classical
  -- `I` is a minimal prime over `ann = colon N {x}`
  set ann := colon N {x}
  -- there exists an integer `n ≠ 0` and an ideal `J` satisfying `I ^ n * J ≤ ann` and `¬ J ≠ I`
  have key : ∃ n ≠ 0, ∃ J : Ideal R, I ^ n * J ≤ ann ∧ ¬ J ≤ I := by
    -- let `n` be large enough so that `ann.radical ^ n ≤ ann` (uses Noetherian)
    obtain ⟨n, hn⟩ := ann.exists_radical_pow_le_of_fg ann.radical.fg_of_isNoetherianRing
    have hn0 : n ≠ 0 := by contrapose hn; simpa [hn, ann]
    -- then take `J` to be the product of the other minimal primes raised to the `n`th power
    have h := ann.finite_minimalPrimes_of_isNoetherianRing R
    rw [← ann.sInf_minimalPrimes, ← h.coe_toFinset, ← h.toFinset.inf_id_eq_sInf,
      ← Finset.insert_erase (h.mem_toFinset.mpr hI), Finset.inf_insert, id_eq] at hn
    grw [← Ideal.mul_le_inf, mul_pow] at hn
    refine ⟨n, hn0, ((h.toFinset.erase I).inf id) ^ n, hn, ?_⟩
    have (K : Ideal R) (hKI : K ≤ I) (hK : K ∈ ann.minimalPrimes) : K = I :=
      le_antisymm hKI (hI.2 hK.1 hKI)
    simpa [hI.1.1.pow_le_iff hn0, hI.1.1.inf_le', imp_not_comm, not_imp_not]
  obtain ⟨hn0, J, hJ, hJI⟩ := Nat.find_spec key
  -- let `n` be minimal such that there exists an ideal `J` with `I ^ n * J ≤ ann` and `¬ J ≠ I`
  set n := Nat.find key
  -- the minimality of `n` will allow us to pick `x'` from the ideal `K = I ^ (n - 1) * J`
  let K := I ^ (n - 1) * J
  -- we want `I = colon N {x'}`, and we have `I ≤ colon N {y • x}` for every `y ∈ K` (uses `n ≠ 0`)
  have step1 : ∀ y ∈ K, I ≤ colon N {y • x} := by
    intro y hy p hp
    rw [mem_colon_singleton, smul_smul, ← mem_colon_singleton]
    apply hJ
    simpa [K, ← mul_assoc, mul_pow_sub_one hn0] using mul_mem_mul hp hy
  clear hn0
  -- so it suffices to find a single `y ∈ K` with `colon N {y • x} ≤ I`
  suffices step2 : ∃ y : K, colon N {y • x} ≤ I by
    obtain ⟨y, hyI⟩ := step2
    exact ⟨y • x, le_antisymm (step1 y y.2) hyI⟩
  -- if not, then for every `y ∈ K`, there exists an `f y ∈ colon N {y • x}` with `f y ∉ I`
  by_contra! h'
  simp only [SetLike.not_le_iff_exists] at h'
  choose f g h using h'
  -- let `s` be a finite generating set for `K`
  obtain ⟨s, hs⟩ : (⊤ : Submodule R K).FG := Module.Finite.fg_top
  -- let `z` be the product of these finitely many `f y`'s
  let z := ∏ y ∈ s, f y
  -- then `z ∉ I`
  have hz : z ∉ I := by
    simp only [z, hI.1.1.prod_mem_iff, not_exists, not_and_or]
    exact fun i ↦ Or.inr (h i)
  -- and `K ≤ colon N {z • x}`
  have hz' : K ≤ colon N {z • x} := by
    rw [← (map_injective_of_injective K.subtype_injective).eq_iff, map_subtype_top] at hs
    rw [← hs, map_span, span_le, Set.image_subset_iff]
    intro i hi
    rw [Set.mem_preimage, SetLike.mem_coe, mem_colon_singleton, smul_comm, ← mem_colon_singleton]
    obtain ⟨y, hy : z = f i * y⟩ := Finset.dvd_prod_of_mem f hi
    exact hy ▸ Ideal.mul_mem_right y _ (g i)
  -- or equivalently `K * Ideal.span {z} ≤ ann`
  replace hz' : K * Ideal.span {z} ≤ ann := by
    rw [mul_comm, Ideal.span_singleton_mul_le_iff]
    intro i hi
    simpa only [ann, mem_colon_singleton, mul_comm, mul_smul] using hz' hi
  -- but now `K = I ^ (n - 1) * J` contradicts the minimality of `n`
  have hK : I ^ (n - 1) * (J * Ideal.span {z}) ≤ ann ∧ ¬ J * Ideal.span {z} ≤ I := by
    rw [← mul_assoc, hI.1.1.mul_le, not_or, Ideal.span_singleton_le_iff_mem]
    exact ⟨hz', hJI, hz⟩
  by_cases hn' : n - 1 = 0
  · simp [K, show n = 1 by grind] at hz'
    exact (hK.2 (hz'.trans hI.1.2)).elim
  · grind [Nat.find_min' key ⟨hn', J * Ideal.span {z}, hK⟩]

end Submodule
