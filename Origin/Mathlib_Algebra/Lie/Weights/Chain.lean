/-
Extracted from Algebra/Lie/Weights/Chain.lean
Genuine: 5 of 6 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Chains of roots and weights

Given roots `α` and `β` of a Lie algebra, together with elements `x` in the `α`-root space and
`y` in the `β`-root space, it follows from the Leibniz identity that `⁅x, y⁆` is either zero or
belongs to the `α + β`-root space. Iterating this operation leads to the study of families of
roots of the form `k • α + β`. Such a family is known as the `α`-chain through `β` (or sometimes,
the `α`-string through `β`) and the study of the sum of the corresponding root spaces is an
important technique.

More generally if `α` is a root and `χ` is a weight of a representation, it is useful to study the
`α`-chain through `χ`.

We provide basic definitions and results to support `α`-chain techniques in this file.

## Main definitions / results

* `LieModule.exists₂_genWeightSpace_smul_add_eq_bot`: given weights `χ₁`, `χ₂` if `χ₁ ≠ 0`, we can
  find `p < 0` and `q > 0` such that the weight spaces `p • χ₁ + χ₂` and `q • χ₁ + χ₂` are both
  trivial.
* `LieModule.genWeightSpaceChain`: given weights `χ₁`, `χ₂` together with integers `p` and `q`,
  this is the sum of the weight spaces `k • χ₁ + χ₂` for `p < k < q`.
* `LieModule.trace_toEnd_genWeightSpaceChain_eq_zero`: given a root `α` relative to a Cartan
  subalgebra `H`, there is a natural ideal `corootSpace α` in `H`. This lemma
  states that this ideal acts by trace-zero endomorphisms on the sum of root spaces of any
  `α`-chain, provided the weight spaces at the endpoints are both trivial.
* `LieModule.exists_forall_mem_corootSpace_smul_add_eq_zero`: given a (potential) root
  `α` relative to a Cartan subalgebra `H`, if we restrict to the ideal
  `corootSpace α` of `H`, we may find an integral linear combination between
  `α` and any weight `χ` of a representation.

## TODO

It should be possible to unify some of the definitions here such as `LieModule.chainBotCoeff`,
`LieModule.chainTopCoeff` with corresponding definitions such as `RootPairing.chainBotCoeff`,
`RootPairing.chainTopCoeff`. This is not quite trivial since:
* The definitions here allow for chains in representations of Lie algebras.
* The proof that the roots of a Lie algebra are a root system currently depends on these results.
  (This can be resolved by proving the root reflection formula using the approach outlined in
  Bourbaki Ch. VIII §2.2 Lemma 1 (page 80 of English translation, 88 of English PDF).)

-/

open Module Function Set

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

namespace LieModule

section IsNilpotent

variable [LieRing.IsNilpotent L] (χ₁ χ₂ : L → R) (p q : ℤ)

variable [IsAddTorsionFree R] [IsDomain R] [IsTorsionFree R M] [IsNoetherian R M] (hχ₁ : χ₁ ≠ 0)

include hχ₁

lemma eventually_genWeightSpace_smul_add_eq_bot :
    ∀ᶠ (k : ℕ) in Filter.atTop, genWeightSpace M (k • χ₁ + χ₂) = ⊥ := by
  let f : ℕ → L → R := fun k ↦ k • χ₁ + χ₂
  suffices Injective f by
    rw [← Nat.cofinite_eq_atTop, Filter.eventually_cofinite, ← finite_image_iff this.injOn]
    apply (finite_genWeightSpace_ne_bot R L M).subset
    simp [f]
  intro k l hkl
  replace hkl : (k : ℤ) • χ₁ = (l : ℤ) • χ₁ := by
    simpa only [f, add_left_inj, natCast_zsmul] using hkl
  exact Nat.cast_inj.mp <| smul_left_injective ℤ hχ₁ hkl

lemma exists_genWeightSpace_smul_add_eq_bot :
    ∃ k > 0, genWeightSpace M (k • χ₁ + χ₂) = ⊥ :=
  (Nat.eventually_pos.and <| eventually_genWeightSpace_smul_add_eq_bot M χ₁ χ₂ hχ₁).exists

lemma exists₂_genWeightSpace_smul_add_eq_bot :
    ∃ᵉ (p < (0 : ℤ)) (q > (0 : ℤ)),
      genWeightSpace M (p • χ₁ + χ₂) = ⊥ ∧
      genWeightSpace M (q • χ₁ + χ₂) = ⊥ := by
  obtain ⟨q, hq₀, hq⟩ := exists_genWeightSpace_smul_add_eq_bot M χ₁ χ₂ hχ₁
  obtain ⟨p, hp₀, hp⟩ := exists_genWeightSpace_smul_add_eq_bot M (-χ₁) χ₂ (neg_ne_zero.mpr hχ₁)
  refine ⟨-(p : ℤ), by simpa, q, by simpa, ?_, ?_⟩
  · rw [neg_smul, ← smul_neg, natCast_zsmul]
    exact hp
  · rw [natCast_zsmul]
    exact hq

end

def genWeightSpaceChain : LieSubmodule R L M :=
  ⨆ k ∈ Ioo p q, genWeightSpace M (k • χ₁ + χ₂)

lemma genWeightSpaceChain_def' :
    genWeightSpaceChain M χ₁ χ₂ p q = ⨆ k ∈ Finset.Ioo p q, genWeightSpace M (k • χ₁ + χ₂) := by
  have : ∀ (k : ℤ), k ∈ Ioo p q ↔ k ∈ Finset.Ioo p q := by simp
  simp_rw [genWeightSpaceChain_def, this]
