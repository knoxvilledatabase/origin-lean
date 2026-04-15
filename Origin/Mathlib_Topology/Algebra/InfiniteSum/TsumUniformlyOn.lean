/-
Extracted from Topology/Algebra/InfiniteSum/TsumUniformlyOn.lean
Genuine: 5 of 6 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Differentiability of sum of functions

We prove some `HasSumUniformlyOn` versions of theorems from
`Mathlib.Analysis.NormedSpace.FunctionSeries`.

Alongside this we prove `derivWithin_tsum` which states that the derivative of a series of functions
is the sum of the derivatives, under suitable conditions we also prove an `iteratedDerivWithin`
version.

-/

open Set Metric TopologicalSpace Function Filter

open scoped Topology NNReal

section UniformlyOn

variable {α β F : Type*} [NormedAddCommGroup F] [CompleteSpace F] {u : α → ℝ}

theorem HasSumUniformlyOn.of_norm_le_summable {f : α → β → F} (hu : Summable u) {s : Set β}
    (hfu : ∀ n x, x ∈ s → ‖f n x‖ ≤ u n) : HasSumUniformlyOn f (fun x ↦ ∑' n, f n x) s := by
  simp [hasSumUniformlyOn_iff_tendstoUniformlyOn, tendstoUniformlyOn_tsum hu hfu]

theorem HasSumUniformlyOn.of_norm_le_summable_eventually {ι : Type*} {f : ι → β → F} {u : ι → ℝ}
    (hu : Summable u) {s : Set β} (hfu : ∀ᶠ n in cofinite, ∀ x ∈ s, ‖f n x‖ ≤ u n) :
    HasSumUniformlyOn f (fun x ↦ ∑' n, f n x) s := by
  simp [hasSumUniformlyOn_iff_tendstoUniformlyOn,
    tendstoUniformlyOn_tsum_of_cofinite_eventually hu hfu]

lemma SummableLocallyUniformlyOn.of_locally_bounded_eventually [TopologicalSpace β]
    [LocallyCompactSpace β] {f : α → β → F} {s : Set β} (hs : IsOpen s)
    (hu : ∀ K ⊆ s, IsCompact K → ∃ u : α → ℝ, Summable u ∧
    ∀ᶠ n in cofinite, ∀ k ∈ K, ‖f n k‖ ≤ u n) : SummableLocallyUniformlyOn f s := by
  apply HasSumLocallyUniformlyOn.summableLocallyUniformlyOn (g := fun x ↦ ∑' n, f n x)
  rw [hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn,
    tendstoLocallyUniformlyOn_iff_forall_isCompact hs]
  intro K hK hKc
  obtain ⟨u, hu1, hu2⟩ := hu K hK hKc
  exact tendstoUniformlyOn_tsum_of_cofinite_eventually hu1 hu2

lemma SummableLocallyUniformlyOn_of_locally_bounded [TopologicalSpace β] [LocallyCompactSpace β]
    {f : α → β → F} {s : Set β} (hs : IsOpen s)
    (hu : ∀ K ⊆ s, IsCompact K → ∃ u : α → ℝ, Summable u ∧ ∀ n, ∀ k ∈ K, ‖f n k‖ ≤ u n) :
    SummableLocallyUniformlyOn f s := by
  apply SummableLocallyUniformlyOn.of_locally_bounded_eventually hs
  intro K hK hKc
  obtain ⟨u, hu1, hu2⟩ := hu K hK hKc
  exact ⟨u, hu1, by filter_upwards using hu2⟩

end UniformlyOn

variable {ι 𝕜 F : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {s : Set 𝕜}

theorem iteratedDerivWithin_tsum {f : ι → 𝕜 → F} (m : ℕ) (hs : IsOpen s)
    {x : 𝕜} (hx : x ∈ s) (hsum : ∀ t ∈ s, Summable (fun n : ι ↦ f n t))
    (h : ∀ k, 1 ≤ k → k ≤ m → SummableLocallyUniformlyOn
      (fun n ↦ (iteratedDerivWithin k (fun z ↦ f n z) s)) s)
    (hf2 : ∀ n k r, k ≤ m → r ∈ s →
      DifferentiableAt 𝕜 (iteratedDerivWithin k (fun z ↦ f n z) s) r) :
    iteratedDerivWithin m (fun z ↦ ∑' n, f n z) s x = ∑' n, iteratedDerivWithin m (f n) s x := by
  induction m generalizing x with
  | zero => simp
  | succ m hm =>
    simp_rw [iteratedDerivWithin_succ]
    rw [← derivWithin_tsum hs hx _ _ (fun n r hr ↦ hf2 n m r (by lia) hr)]
    · exact derivWithin_congr (fun t ht ↦ hm ht (fun k hk1 hkm ↦ h k hk1 (by lia))
          (fun k r e hr he ↦ hf2 k r e (by lia) he)) (hm hx (fun k hk1 hkm ↦ h k hk1 (by lia))
          (fun k r e hr he ↦ hf2 k r e (by lia) he))
    · intro r hr
      by_cases hm2 : m = 0
      · simp [hm2, hsum r hr]
      · exact ((h m (by lia) (by lia)).summable hr).congr (fun _ ↦ by simp)
    · exact SummableLocallyUniformlyOn_congr
        (fun _ _ ht ↦ by rw [iteratedDerivWithin_succ]) (h (m + 1) (by lia) (by lia))
