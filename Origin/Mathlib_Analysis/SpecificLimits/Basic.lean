/-
Extracted from Analysis/SpecificLimits/Basic.lean
Genuine: 17 of 20 | Dissolved: 3 | Infrastructure: 0
-/
import Origin.Core

/-!
# A collection of specific limit computations

This file, by design, is independent of `NormedSpace` in the import hierarchy.  It contains
important specific limit computations in metric spaces, in ordered rings/fields, and in specific
instances of these such as `ℝ`, `ℝ≥0` and `ℝ≥0∞`.
-/

assert_not_exists Module.Basis NormedSpace

noncomputable section

open Set Function Filter Finset Metric Topology Nat uniformity NNReal ENNReal

variable {α : Type*} {β : Type*} {ι : Type*}

theorem NNRat.tendsto_inv_atTop_nhds_zero_nat : Tendsto (fun n : ℕ ↦ (n : ℚ≥0)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

theorem NNRat.tendsto_algebraMap_inv_atTop_nhds_zero_nat (𝕜 : Type*) [Semiring 𝕜]
    [Algebra ℚ≥0 𝕜] [TopologicalSpace 𝕜] [ContinuousSMul ℚ≥0 𝕜] :
    Tendsto (algebraMap ℚ≥0 𝕜 ∘ fun n : ℕ ↦ (n : ℚ≥0)⁻¹) atTop (𝓝 0) := by
  convert (continuous_algebraMap ℚ≥0 𝕜).continuousAt.tendsto.comp
    tendsto_inv_atTop_nhds_zero_nat
  rw [map_zero]

theorem tendsto_inv_atTop_nhds_zero_nat {𝕜 : Type*} [DivisionSemiring 𝕜] [CharZero 𝕜]
    [TopologicalSpace 𝕜] [ContinuousSMul ℚ≥0 𝕜] :
    Tendsto (fun n : ℕ ↦ (n : 𝕜)⁻¹) atTop (𝓝 0) := by
  convert NNRat.tendsto_algebraMap_inv_atTop_nhds_zero_nat 𝕜
  simp

theorem tendsto_const_div_atTop_nhds_zero_nat {𝕜 : Type*} [DivisionSemiring 𝕜] [CharZero 𝕜]
    [TopologicalSpace 𝕜] [ContinuousSMul ℚ≥0 𝕜] [ContinuousMul 𝕜] (C : 𝕜) :
    Tendsto (fun n : ℕ ↦ C / n) atTop (𝓝 0) := by
  simpa only [mul_zero, div_eq_mul_inv] using
    (tendsto_const_nhds (x := C)).mul tendsto_inv_atTop_nhds_zero_nat

theorem tendsto_one_div_atTop_nhds_zero_nat {𝕜 : Type*} [DivisionSemiring 𝕜] [CharZero 𝕜]
    [TopologicalSpace 𝕜] [ContinuousSMul ℚ≥0 𝕜] :
    Tendsto (fun n : ℕ ↦ 1 / (n : 𝕜)) atTop (𝓝 0) := by
  simp [tendsto_inv_atTop_nhds_zero_nat]

theorem EReal.tendsto_const_div_atTop_nhds_zero_nat {C : EReal} (h : C ≠ ⊥) (h' : C ≠ ⊤) :
    Tendsto (fun n : ℕ ↦ C / n) atTop (𝓝 0) := by
  have : (fun n : ℕ ↦ C / n) = fun n : ℕ ↦ ((C.toReal / n : ℝ) : EReal) := by
    ext n
    nth_rw 1 [← coe_toReal h' h, ← coe_coe_eq_natCast n, ← coe_div C.toReal n]
  rw [this, ← coe_zero, tendsto_coe]
  exact _root_.tendsto_const_div_atTop_nhds_zero_nat C.toReal

theorem tendsto_one_div_add_atTop_nhds_zero_nat {𝕜 : Type*} [DivisionSemiring 𝕜] [CharZero 𝕜]
    [TopologicalSpace 𝕜] [ContinuousSMul ℚ≥0 𝕜] :
    Tendsto (fun n : ℕ ↦ 1 / ((n : 𝕜) + 1)) atTop (𝓝 0) :=
  suffices Tendsto (fun n : ℕ ↦ 1 / (↑(n + 1) : 𝕜)) atTop (𝓝 0) by simpa
  (tendsto_add_atTop_iff_nat 1).2 tendsto_one_div_atTop_nhds_zero_nat

theorem tendsto_algebraMap_inv_atTop_nhds_zero_nat {𝕜 : Type*} (A : Type*)
    [Semifield 𝕜] [CharZero 𝕜] [TopologicalSpace 𝕜] [ContinuousSMul ℚ≥0 𝕜]
    [Semiring A] [Algebra 𝕜 A] [TopologicalSpace A] [ContinuousSMul 𝕜 A] :
    Tendsto (algebraMap 𝕜 A ∘ fun n : ℕ ↦ (n : 𝕜)⁻¹) atTop (𝓝 0) := by
  convert (continuous_algebraMap 𝕜 A).continuousAt.tendsto.comp tendsto_inv_atTop_nhds_zero_nat
  rw [map_zero]

theorem tendsto_natCast_div_add_atTop {𝕜 : Type*} [DivisionSemiring 𝕜] [TopologicalSpace 𝕜]
    [CharZero 𝕜] [ContinuousSMul ℚ≥0 𝕜] [IsTopologicalSemiring 𝕜] [ContinuousInv₀ 𝕜] (x : 𝕜) :
    Tendsto (fun n : ℕ ↦ (n : 𝕜) / (n + x)) atTop (𝓝 1) := by
  convert Tendsto.congr' ((eventually_ne_atTop 0).mp (Eventually.of_forall fun n hn ↦ _)) _
  · exact fun n : ℕ ↦ 1 / (1 + x / n)
  · simp [Nat.cast_ne_zero.mpr hn, add_div']
  · have : 𝓝 (1 : 𝕜) = 𝓝 (1 / (1 + x * (0 : 𝕜))) := by
      rw [mul_zero, add_zero, div_one]
    rw [this]
    refine tendsto_const_nhds.div (tendsto_const_nhds.add ?_) (by simp)
    simp_rw [div_eq_mul_inv]
    exact tendsto_const_nhds.mul tendsto_inv_atTop_nhds_zero_nat

-- DISSOLVED: tendsto_add_mul_div_add_mul_atTop_nhds

theorem tendsto_mod_div_atTop_nhds_zero_nat {m : ℕ} (hm : 0 < m) :
    Tendsto (fun n : ℕ => ((n % m : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  have h0 : ∀ᶠ n : ℕ in atTop, 0 ≤ (fun n : ℕ => ((n % m : ℕ) : ℝ)) n := by aesop
  exact tendsto_bdd_div_atTop_nhds_zero h0
    (.of_forall (fun n ↦ cast_le.mpr (mod_lt n hm).le)) tendsto_natCast_atTop_atTop

-- DISSOLVED: tendsto_mul_add_inv_atTop_nhds_zero

-- DISSOLVED: Filter.EventuallyEq.div_mul_cancel

theorem Filter.EventuallyEq.div_mul_cancel_atTop {α K : Type*}
    [DivisionSemiring K] [LinearOrder K] [IsStrictOrderedRing K]
    {f g : α → K} {l : Filter α} (hg : Tendsto g l atTop) :
    (fun x ↦ f x / g x * g x) =ᶠ[l] fun x ↦ f x :=
  div_mul_cancel <| hg.mono_right <| le_principal_iff.mpr <|
    mem_of_superset (Ioi_mem_atTop 0) <| by simp

theorem Filter.Tendsto.num {α K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [TopologicalSpace K] [OrderTopology K]
    {f g : α → K} {l : Filter α} (hg : Tendsto g l atTop) {a : K} (ha : 0 < a)
    (hlim : Tendsto (fun x => f x / g x) l (𝓝 a)) :
    Tendsto f l atTop :=
  (hlim.pos_mul_atTop ha hg).congr' (EventuallyEq.div_mul_cancel_atTop hg)

theorem Filter.Tendsto.den {α K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [TopologicalSpace K] [OrderTopology K]
    [ContinuousInv K] {f g : α → K} {l : Filter α} (hf : Tendsto f l atTop) {a : K} (ha : 0 < a)
    (hlim : Tendsto (fun x => f x / g x) l (𝓝 a)) :
    Tendsto g l atTop :=
  have hlim' : Tendsto (fun x => g x / f x) l (𝓝 a⁻¹) := by
    simp_rw [← inv_div (f _)]
    exact Filter.Tendsto.inv (f := fun x => f x / g x) hlim
  (hlim'.pos_mul_atTop (inv_pos_of_pos ha) hf).congr' (.div_mul_cancel_atTop hf)

theorem Filter.Tendsto.num_atTop_iff_den_atTop {α K : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [TopologicalSpace K]
    [OrderTopology K] [ContinuousInv K] {f g : α → K} {l : Filter α} {a : K} (ha : 0 < a)
    (hlim : Tendsto (fun x => f x / g x) l (𝓝 a)) :
    Tendsto f l atTop ↔ Tendsto g l atTop :=
  ⟨fun hf ↦ hf.den ha hlim, fun hg ↦ hg.num ha hlim⟩

/-! ### Powers -/

theorem tendsto_add_one_pow_atTop_atTop_of_pos
    [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [Archimedean α] {r : α}
    (h : 0 < r) : Tendsto (fun n : ℕ ↦ (r + 1) ^ n) atTop atTop :=
  tendsto_atTop_atTop_of_monotone' (pow_right_mono₀ <| le_add_of_nonneg_left h.le) <|
    not_bddAbove_iff.2 fun _ ↦ Set.exists_range_iff.2 <| add_one_pow_unbounded_of_pos _ h

theorem tendsto_pow_atTop_atTop_of_one_lt
    [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α] [Archimedean α] {r : α}
    (h : 1 < r) : Tendsto (fun n : ℕ ↦ r ^ n) atTop atTop := by
  obtain ⟨r, r0, rfl⟩ := exists_pos_add_of_lt' h
  rw [add_comm]
  exact tendsto_add_one_pow_atTop_atTop_of_pos r0

theorem tendsto_pow_atTop_nhds_zero_of_lt_one {𝕜 : Type*}
    [Semifield 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [ExistsAddOfLE 𝕜] [Archimedean 𝕜]
    [TopologicalSpace 𝕜] [OrderTopology 𝕜] {r : 𝕜} (h₁ : 0 ≤ r) (h₂ : r < 1) :
    Tendsto (fun n : ℕ ↦ r ^ n) atTop (𝓝 0) :=
  h₁.eq_or_lt.elim
    (fun hr ↦ (tendsto_add_atTop_iff_nat 1).mp <| by
      simp [_root_.pow_succ, ← hr])
    (fun hr ↦
      have := (one_lt_inv₀ hr).2 h₂ |> tendsto_pow_atTop_atTop_of_one_lt
      (tendsto_inv_atTop_zero.comp this).congr fun n ↦ by simp)
