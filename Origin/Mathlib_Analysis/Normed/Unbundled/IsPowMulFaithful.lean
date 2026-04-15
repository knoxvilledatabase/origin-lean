/-
Extracted from Analysis/Normed/Unbundled/IsPowMulFaithful.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Equivalent power-multiplicative norms

In this file, we prove [BGR, Proposition 3.1.5/1][bosch-guntzer-remmert]: if `R` is a normed
commutative ring and `f₁` and `f₂` are two power-multiplicative `R`-algebra norms on `S`, then if
`f₁` and `f₂` are equivalent on every subring `R[y]` for `y : S`, it follows that `f₁ = f₂`.

## Main Results
* `eq_of_powMul_faithful` : the proof of [BGR, Proposition 3.1.5/1][bosch-guntzer-remmert].

## References
* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

## Tags

norm, equivalent, power-multiplicative
-/

open Filter Real Algebra

open scoped Topology

theorem contraction_of_isPowMul_of_boundedWrt {F : Type*} {α : outParam (Type*)} [Ring α]
    [FunLike F α ℝ] [RingSeminormClass F α ℝ] {β : Type*} [Ring β] (nα : F) {nβ : β → ℝ}
    (hβ : IsPowMul nβ) {f : α →+* β} (hf : f.IsBoundedWrt nα nβ) (x : α) : nβ (f x) ≤ nα x := by
  obtain ⟨C, hC0, hC⟩ := hf
  have hlim : Tendsto (fun n : ℕ => C ^ (1 / (n : ℝ)) * nα x) atTop (𝓝 (nα x)) := by
    nth_rewrite 2 [← one_mul (nα x)]
    exact ((rpow_zero C ▸ ContinuousAt.tendsto (continuousAt_const_rpow (ne_of_gt hC0))).comp
      (tendsto_const_div_atTop_nhds_zero_nat 1)).mul tendsto_const_nhds
  apply ge_of_tendsto hlim
  simp only [eventually_atTop, ge_iff_le]
  use 1
  intro n hn
  have h : (C ^ (1 / n : ℝ)) ^ n = C := by
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn)
    rw [← rpow_natCast, ← rpow_mul hC0.le, one_div, inv_mul_cancel₀ hn0, rpow_one]
  apply le_of_pow_le_pow_left₀ (ne_of_gt hn) (by positivity)
  · rw [mul_pow, h, ← hβ _ hn, ← map_pow]
    apply le_trans (hC (x ^ n))
    rw [mul_le_mul_iff_right₀ hC0]
    exact map_pow_le_pow _ _ (Nat.one_le_iff_ne_zero.mp hn)

theorem contraction_of_isPowMul {α β : Type*} [SeminormedRing α] [SeminormedRing β]
    (hβ : IsPowMul (norm : β → ℝ)) {f : α →+* β} (hf : f.IsBounded) (x : α) : norm (f x) ≤ norm x :=
  contraction_of_isPowMul_of_boundedWrt (SeminormedRing.toRingSeminorm α) hβ hf x

theorem eq_seminorms {F : Type*} {α : outParam (Type*)} [Ring α] [FunLike F α ℝ]
    [RingSeminormClass F α ℝ] {f g : F} (hfpm : IsPowMul f) (hgpm : IsPowMul g)
    (hfg : ∃ (r : ℝ) (_ : 0 < r), ∀ a : α, f a ≤ r * g a)
    (hgf : ∃ (r : ℝ) (_ : 0 < r), ∀ a : α, g a ≤ r * f a) : f = g := by
  obtain ⟨r, hr0, hr⟩ := hfg
  obtain ⟨s, hs0, hs⟩ := hgf
  have hle : RingHom.IsBoundedWrt f g (RingHom.id _) := ⟨s, hs0, hs⟩
  have hge : RingHom.IsBoundedWrt g f (RingHom.id _) := ⟨r, hr0, hr⟩
  rw [← Function.Injective.eq_iff DFunLike.coe_injective']
  ext x
  exact le_antisymm (contraction_of_isPowMul_of_boundedWrt g hfpm hge x)
    (contraction_of_isPowMul_of_boundedWrt f hgpm hle x)

variable {R S : Type*} [NormedCommRing R] [CommRing S] [Algebra R S]
