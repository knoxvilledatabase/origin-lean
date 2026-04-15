/-
Extracted from Analysis/SpecificLimits/Normed.lean
Genuine: 29 of 31 | Dissolved: 1 | Infrastructure: 1
-/
import Origin.Core

/-!
# A collection of specific limit computations

This file contains important specific limit computations in (semi-)normed groups/rings/spaces, as
well as such computations in `ℝ` when the natural proof passes through a fact about normed spaces.
-/

noncomputable section

open Set Function Filter Finset Metric Module Asymptotics Topology Nat NNReal ENNReal

open scoped Ring

variable {α : Type*}

theorem tendsto_natCast_atTop_cobounded
    [NormedRing α] [NormSMulClass ℤ α] [Nontrivial α] :
    Tendsto Nat.cast atTop (Bornology.cobounded α) := by
  rw [← tendsto_norm_atTop_iff_cobounded]
  simpa [norm_natCast_eq_mul_norm_one] using tendsto_natCast_atTop_atTop
    |>.atTop_mul_const (norm_pos_iff.mpr one_ne_zero)

theorem tendsto_intCast_atBot_sup_atTop_cobounded
    [NormedRing α] [NormSMulClass ℤ α] [Nontrivial α] :
    Tendsto Int.cast (atBot ⊔ atTop) (Bornology.cobounded α) := by
  rw [← tendsto_norm_atTop_iff_cobounded]
  simpa [norm_intCast_eq_abs_mul_norm_one] using tendsto_intCast_atTop_atTop
    |>.comp (tendsto_abs_atBot_atTop.sup tendsto_abs_atTop_atTop)
    |>.atTop_mul_const (norm_pos_iff.mpr one_ne_zero)

theorem tendsto_intCast_atBot_cobounded
    [NormedRing α] [NormSMulClass ℤ α] [Nontrivial α] :
    Tendsto Int.cast atBot (Bornology.cobounded α) :=
  tendsto_intCast_atBot_sup_atTop_cobounded.mono_left le_sup_left

theorem tendsto_intCast_atTop_cobounded
    [NormedRing α] [NormSMulClass ℤ α] [Nontrivial α] :
    Tendsto Int.cast atTop (Bornology.cobounded α) :=
  tendsto_intCast_atBot_sup_atTop_cobounded.mono_left le_sup_right

/-! ### Powers -/

theorem isLittleO_pow_pow_of_lt_left {r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁) (h₂ : r₁ < r₂) :
    (fun n : ℕ ↦ r₁ ^ n) =o[atTop] fun n ↦ r₂ ^ n :=
  have H : 0 < r₂ := h₁.trans_lt h₂
  (isLittleO_of_tendsto fun _ hn ↦ False.elim <| H.ne' <| eq_zero_of_pow_eq_zero hn) <|
    (tendsto_pow_atTop_nhds_zero_of_lt_one
      (div_nonneg h₁ (h₁.trans h₂.le)) ((div_lt_one H).2 h₂)).congr fun _ ↦ div_pow _ _ _

theorem isBigO_pow_pow_of_le_left {r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁) (h₂ : r₁ ≤ r₂) :
    (fun n : ℕ ↦ r₁ ^ n) =O[atTop] fun n ↦ r₂ ^ n :=
  h₂.eq_or_lt.elim (fun h ↦ h ▸ isBigO_refl _ _) fun h ↦ (isLittleO_pow_pow_of_lt_left h₁ h).isBigO

theorem isLittleO_pow_pow_of_abs_lt_left {r₁ r₂ : ℝ} (h : |r₁| < |r₂|) :
    (fun n : ℕ ↦ r₁ ^ n) =o[atTop] fun n ↦ r₂ ^ n := by
  refine (IsLittleO.of_norm_left ?_).of_norm_right
  exact (isLittleO_pow_pow_of_lt_left (abs_nonneg r₁) h).congr (pow_abs r₁) (pow_abs r₂)

open List in

theorem TFAE_exists_lt_isLittleO_pow (f : ℕ → ℝ) (R : ℝ) :
    TFAE
      [∃ a ∈ Ioo (-R) R, f =o[atTop] (a ^ ·), ∃ a ∈ Ioo 0 R, f =o[atTop] (a ^ ·),
        ∃ a ∈ Ioo (-R) R, f =O[atTop] (a ^ ·), ∃ a ∈ Ioo 0 R, f =O[atTop] (a ^ ·),
        ∃ a < R, ∃ C : ℝ, (0 < C ∨ 0 < R) ∧ ∀ n, |f n| ≤ C * a ^ n,
        ∃ a ∈ Ioo 0 R, ∃ C > 0, ∀ n, |f n| ≤ C * a ^ n, ∃ a < R, ∀ᶠ n in atTop, |f n| ≤ a ^ n,
        ∃ a ∈ Ioo 0 R, ∀ᶠ n in atTop, |f n| ≤ a ^ n] := by
  have A : Ico 0 R ⊆ Ioo (-R) R :=
    fun x hx ↦ ⟨(neg_lt_zero.2 (hx.1.trans_lt hx.2)).trans_le hx.1, hx.2⟩
  have B : Ioo 0 R ⊆ Ioo (-R) R := Subset.trans Ioo_subset_Ico_self A
  -- First we prove that 1-4 are equivalent using 2 → 3 → 4, 1 → 3, and 2 → 1
  tfae_have 1 → 3 := fun ⟨a, ha, H⟩ ↦ ⟨a, ha, H.isBigO⟩
  tfae_have 2 → 1 := fun ⟨a, ha, H⟩ ↦ ⟨a, B ha, H⟩
  tfae_have 3 → 2
  | ⟨a, ha, H⟩ => by
    rcases exists_between (abs_lt.2 ha) with ⟨b, hab, hbR⟩
    exact ⟨b, ⟨(abs_nonneg a).trans_lt hab, hbR⟩,
      H.trans_isLittleO (isLittleO_pow_pow_of_abs_lt_left (hab.trans_le (le_abs_self b)))⟩
  tfae_have 2 → 4 := fun ⟨a, ha, H⟩ ↦ ⟨a, ha, H.isBigO⟩
  tfae_have 4 → 3 := fun ⟨a, ha, H⟩ ↦ ⟨a, B ha, H⟩
  -- Add 5 and 6 using 4 → 6 → 5 → 3
  tfae_have 4 → 6
  | ⟨a, ha, H⟩ => by
    rcases bound_of_isBigO_nat_atTop H with ⟨C, hC₀, hC⟩
    refine ⟨a, ha, C, hC₀, fun n ↦ ?_⟩
    simpa only [Real.norm_eq_abs, abs_pow, abs_of_nonneg ha.1.le] using hC (pow_ne_zero n ha.1.ne')
  tfae_have 6 → 5 := fun ⟨a, ha, C, H₀, H⟩ ↦ ⟨a, ha.2, C, Or.inl H₀, H⟩
  tfae_have 5 → 3
  | ⟨a, ha, C, h₀, H⟩ => by
    rcases sign_cases_of_C_mul_pow_nonneg fun n ↦ (abs_nonneg _).trans (H n) with (rfl | ⟨hC₀, ha₀⟩)
    · obtain rfl : f = 0 := by
        ext n
        simpa using H n
      simp only [lt_irrefl, false_or] at h₀
      exact ⟨0, ⟨neg_lt_zero.2 h₀, h₀⟩, isBigO_zero _ _⟩
    exact ⟨a, A ⟨ha₀, ha⟩,
      isBigO_of_le' _ fun n ↦ (H n).trans <| mul_le_mul_of_nonneg_left (le_abs_self _) hC₀.le⟩
  -- Add 7 and 8 using 2 → 8 → 7 → 3
  tfae_have 2 → 8
  | ⟨a, ha, H⟩ => by
    refine ⟨a, ha, (H.def zero_lt_one).mono fun n hn ↦ ?_⟩
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, abs_pow, abs_of_pos ha.1] at hn
  tfae_have 8 → 7 := fun ⟨a, ha, H⟩ ↦ ⟨a, ha.2, H⟩
  tfae_have 7 → 3
  | ⟨a, ha, H⟩ => by
    refine ⟨a, A ⟨?_, ha⟩, .of_norm_eventuallyLE H⟩
    exact nonneg_of_eventually_pow_nonneg (H.mono fun n ↦ (abs_nonneg _).trans)
  tfae_finish

theorem isLittleO_pow_const_const_pow_of_one_lt {R : Type*} [NormedRing R] (k : ℕ) {r : ℝ}
    (hr : 1 < r) : (fun n ↦ (n : R) ^ k : ℕ → R) =o[atTop] fun n ↦ r ^ n := by
  have : Tendsto (fun x : ℝ ↦ x ^ k) (𝓝[>] 1) (𝓝 1) :=
    ((continuous_id.pow k).tendsto' (1 : ℝ) 1 (one_pow _)).mono_left inf_le_left
  obtain ⟨r' : ℝ, hr' : r' ^ k < r, h1 : 1 < r'⟩ :=
    ((this.eventually (gt_mem_nhds hr)).and self_mem_nhdsWithin).exists
  have h0 : 0 ≤ r' := zero_le_one.trans h1.le
  suffices (fun n ↦ (n : R) ^ k : ℕ → R) =O[atTop] fun n : ℕ ↦ (r' ^ k) ^ n from
    this.trans_isLittleO (isLittleO_pow_pow_of_lt_left (pow_nonneg h0 _) hr')
  conv in (r' ^ _) ^ _ => rw [← pow_mul, mul_comm, pow_mul]
  suffices ∀ n : ℕ, ‖(n : R)‖ ≤ (r' - 1)⁻¹ * ‖(1 : R)‖ * ‖r' ^ n‖ from
    (isBigO_of_le' _ this).pow _
  intro n
  rw [mul_right_comm]
  refine n.norm_cast_le.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  simpa [_root_.div_eq_inv_mul, Real.norm_eq_abs, abs_of_nonneg h0] using n.cast_le_pow_div_sub h1

theorem isLittleO_coe_const_pow_of_one_lt {R : Type*} [NormedRing R] {r : ℝ} (hr : 1 < r) :
    ((↑) : ℕ → R) =o[atTop] fun n ↦ r ^ n := by
  simpa only [pow_one] using @isLittleO_pow_const_const_pow_of_one_lt R _ 1 _ hr

theorem isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt {R : Type*} [NormedRing R] (k : ℕ)
    {r₁ : R} {r₂ : ℝ} (h : ‖r₁‖ < r₂) :
    (fun n ↦ (n : R) ^ k * r₁ ^ n : ℕ → R) =o[atTop] fun n ↦ r₂ ^ n := by
  by_cases h0 : r₁ = 0
  · refine (isLittleO_zero _ _).congr' (mem_atTop_sets.2 <| ⟨1, fun n hn ↦ ?_⟩) EventuallyEq.rfl
    simp [zero_pow (one_le_iff_ne_zero.1 hn), h0]
  rw [← Ne, ← norm_pos_iff] at h0
  have A : (fun n ↦ (n : R) ^ k : ℕ → R) =o[atTop] fun n ↦ (r₂ / ‖r₁‖) ^ n :=
    isLittleO_pow_const_const_pow_of_one_lt k ((one_lt_div h0).2 h)
  suffices (fun n ↦ r₁ ^ n) =O[atTop] fun n ↦ ‖r₁‖ ^ n by
    simpa [div_mul_cancel₀ _ (pow_pos h0 _).ne', div_pow] using A.mul_isBigO this
  exact .of_norm_eventuallyLE <| eventually_norm_pow_le r₁

theorem tendsto_pow_const_div_const_pow_of_one_lt (k : ℕ) {r : ℝ} (hr : 1 < r) :
    Tendsto (fun n ↦ (n : ℝ) ^ k / r ^ n : ℕ → ℝ) atTop (𝓝 0) :=
  (isLittleO_pow_const_const_pow_of_one_lt k hr).tendsto_div_nhds_zero

theorem tendsto_pow_const_mul_const_pow_of_abs_lt_one (k : ℕ) {r : ℝ} (hr : |r| < 1) :
    Tendsto (fun n ↦ (n : ℝ) ^ k * r ^ n : ℕ → ℝ) atTop (𝓝 0) := by
  by_cases h0 : r = 0
  · exact tendsto_const_nhds.congr'
      (mem_atTop_sets.2 ⟨1, fun n hn ↦ by simp [zero_lt_one.trans_le hn |>.ne', h0]⟩)
  have hr' : 1 < |r|⁻¹ := (one_lt_inv₀ (abs_pos.2 h0)).2 hr
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa [div_eq_mul_inv] using tendsto_pow_const_div_const_pow_of_one_lt k hr'

-- DISSOLVED: tendsto_const_div_pow

theorem tendsto_pow_const_mul_const_pow_of_lt_one (k : ℕ) {r : ℝ} (hr : 0 ≤ r) (h'r : r < 1) :
    Tendsto (fun n ↦ (n : ℝ) ^ k * r ^ n : ℕ → ℝ) atTop (𝓝 0) :=
  tendsto_pow_const_mul_const_pow_of_abs_lt_one k (abs_lt.2 ⟨neg_one_lt_zero.trans_le hr, h'r⟩)

theorem tendsto_self_mul_const_pow_of_abs_lt_one {r : ℝ} (hr : |r| < 1) :
    Tendsto (fun n ↦ n * r ^ n : ℕ → ℝ) atTop (𝓝 0) := by
  simpa only [pow_one] using tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 hr

theorem tendsto_self_mul_const_pow_of_lt_one {r : ℝ} (hr : 0 ≤ r) (h'r : r < 1) :
    Tendsto (fun n ↦ n * r ^ n : ℕ → ℝ) atTop (𝓝 0) := by
  simpa only [pow_one] using tendsto_pow_const_mul_const_pow_of_lt_one 1 hr h'r

theorem tendsto_pow_atTop_nhds_zero_of_norm_lt_one {R : Type*} [SeminormedRing R] {x : R}
    (h : ‖x‖ < 1) :
    Tendsto (fun n : ℕ ↦ x ^ n) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (eventually_norm_pow_le x)
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) h

theorem tendsto_pow_atTop_nhds_zero_of_abs_lt_one {r : ℝ} (h : |r| < 1) :
    Tendsto (fun n : ℕ ↦ r ^ n) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_norm_lt_one h

lemma tendsto_pow_atTop_nhds_zero_iff_norm_lt_one {R : Type*} [SeminormedRing R] [NormMulClass R]
    {x : R} : Tendsto (fun n : ℕ ↦ x ^ n) atTop (𝓝 0) ↔ ‖x‖ < 1 := by
  -- this proof is slightly fiddly since `‖x ^ n‖ = ‖x‖ ^ n` might not hold for `n = 0`
  refine ⟨?_, tendsto_pow_atTop_nhds_zero_of_norm_lt_one⟩
  rw [← abs_of_nonneg (norm_nonneg _), ← tendsto_pow_atTop_nhds_zero_iff,
    tendsto_zero_iff_norm_tendsto_zero]
  apply Tendsto.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn IH => simp [pow_succ, IH]

variable {R S : Type*} [Field R] [Field S] [LinearOrder S] {v w : AbsoluteValue R S}
  [TopologicalSpace S] [IsStrictOrderedRing S] [Archimedean S] [_i : OrderTopology S]

theorem AbsoluteValue.tendsto_div_one_add_pow_nhds_one {v : AbsoluteValue R S} {a : R}
    (ha : v a < 1) : atTop.Tendsto (fun (n : ℕ) ↦ v (1 / (1 + a ^ n))) (𝓝 1) := by
  simp_rw [map_div₀ v, v.map_one]
  apply one_div_one (G := S) ▸ Tendsto.div tendsto_const_nhds _ one_ne_zero
  have h_add := (tendsto_pow_atTop_nhds_zero_of_lt_one (v.nonneg _) ha).const_add 1
  have h_sub := (tendsto_pow_atTop_nhds_zero_of_lt_one (v.nonneg _) ha).const_sub 1
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa using h_sub) (by simpa using h_add)
    (fun n ↦ le_trans (by simp) (v.le_add _ _))
    (fun n ↦ le_trans (v.add_le _ _) (by simp))

theorem AbsoluteValue.tendsto_div_one_add_pow_nhds_zero {v : AbsoluteValue R S} {a : R}
    (ha : 1 < v a) : Filter.Tendsto (fun (n : ℕ) ↦ v (1 / (1 + a ^ n))) Filter.atTop (𝓝 0) := by
  simp_rw [div_eq_mul_inv, one_mul, map_inv₀, fun n ↦ add_comm 1 (a ^ n)]
  refine (tendsto_atTop_mono (fun n ↦ v.le_add _ _) ?_).inv_tendsto_atTop
  simpa using (tendsto_atTop_add_right_of_le _ _ (tendsto_pow_atTop_atTop_of_one_lt ha)
    (fun _ ↦ le_rfl)).congr fun n ↦ (sub_eq_add_neg (v a ^ n) 1).symm

/-! ### Geometric series -/

class HasSummableGeomSeries (K : Type*) [NormedRing K] : Prop where
  summable_geometric_of_norm_lt_one : ∀ (ξ : K), ‖ξ‖ < 1 → Summable (fun n ↦ ξ ^ n)

lemma summable_geometric_of_norm_lt_one {K : Type*} [NormedRing K] [HasSummableGeomSeries K]
    {x : K} (h : ‖x‖ < 1) : Summable (fun n ↦ x ^ n) :=
  HasSummableGeomSeries.summable_geometric_of_norm_lt_one x h

-- INSTANCE (free from Core): {R

section HasSummableGeometricSeries

variable {R : Type*} [NormedRing R]

open NormedSpace

theorem tsum_geometric_le_of_norm_lt_one (x : R) (h : ‖x‖ < 1) :
    ‖∑' n : ℕ, x ^ n‖ ≤ ‖(1 : R)‖ - 1 + (1 - ‖x‖)⁻¹ := by
  by_cases hx : Summable (fun n ↦ x ^ n)
  · rw [hx.tsum_eq_zero_add]
    simp only [_root_.pow_zero]
    refine le_trans (norm_add_le _ _) ?_
    have : ‖∑' b : ℕ, (fun n ↦ x ^ (n + 1)) b‖ ≤ (1 - ‖x‖)⁻¹ - 1 := by
      refine tsum_of_norm_bounded ?_ fun b ↦ norm_pow_le' _ (Nat.succ_pos b)
      convert (hasSum_nat_add_iff' 1).mpr (hasSum_geometric_of_lt_one (norm_nonneg x) h)
      simp
    linarith
  · simp only [tsum_eq_zero_of_not_summable hx, norm_zero]
    nontriviality R
    have : 1 ≤ ‖(1 : R)‖ := one_le_norm_one R
    have : 0 ≤ (1 - ‖x‖)⁻¹ := inv_nonneg.2 (by linarith)
    linarith

variable [HasSummableGeomSeries R]

theorem geom_series_mul_neg (x : R) (h : ‖x‖ < 1) : (∑' i : ℕ, x ^ i) * (1 - x) = 1 :=
  (summable_geometric_of_norm_lt_one h).tsum_pow_mul_one_sub

theorem mul_neg_geom_series (x : R) (h : ‖x‖ < 1) : (1 - x) * ∑' i : ℕ, x ^ i = 1 :=
  (summable_geometric_of_norm_lt_one h).one_sub_mul_tsum_pow

theorem geom_series_succ (x : R) (h : ‖x‖ < 1) : ∑' i : ℕ, x ^ (i + 1) = ∑' i : ℕ, x ^ i - 1 := by
  rw [eq_sub_iff_add_eq, (summable_geometric_of_norm_lt_one h).tsum_eq_zero_add,
    pow_zero, add_comm]

theorem geom_series_mul_shift (x : R) (h : ‖x‖ < 1) :
    x * ∑' i : ℕ, x ^ i = ∑' i : ℕ, x ^ (i + 1) := by
  simp_rw [← (summable_geometric_of_norm_lt_one h).tsum_mul_left, ← _root_.pow_succ']

theorem geom_series_mul_one_add (x : R) (h : ‖x‖ < 1) :
    (1 + x) * ∑' i : ℕ, x ^ i = 2 * ∑' i : ℕ, x ^ i - 1 := by
  rw [add_mul, one_mul, geom_series_mul_shift x h, geom_series_succ x h, two_mul, add_sub_assoc]
