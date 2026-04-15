/-
Extracted from Geometry/Manifold/IntegralCurve/UniformTime.lean
Genuine: 6 of 7 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Uniform time lemma for the global existence of integral curves

## Main results

* `exists_isMIntegralCurve_of_isMIntegralCurveOn`: If there exists `ε > 0` such that the local
  integral curve at each point `x : M` is defined at least on an open interval `Ioo (-ε) ε`, then
  every point on `M` has a global integral curve passing through it.

## Reference

* [Lee, J. M. (2012). _Introduction to Smooth Manifolds_. Springer New York.][lee2012]

## Tags

integral curve, vector field, global existence
-/

open scoped Topology

open Function Manifold Set

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [T2Space M] {γ γ' : ℝ → M} {v : (x : M) → TangentSpace I x} {s s' : Set ℝ} {t₀ : ℝ}

lemma eqOn_of_isMIntegralCurveOn_Ioo [BoundarylessManifold I M]
    (hv : CMDiff 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M))) {x : M}
    (γ : ℝ → ℝ → M) (hγx : ∀ a, γ a 0 = x) (hγ : ∀ a > 0, IsMIntegralCurveOn (γ a) v (Ioo (-a) a))
    {a a' : ℝ} (hpos : 0 < a') (hle : a' ≤ a) :
    EqOn (γ a') (γ a) (Ioo (-a') a') := by
  apply isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless _ hv
    (hγ a' (by positivity)) ((hγ a (lt_of_lt_of_le hpos hle)).mono _)
    (by rw [hγx a, hγx a'])
  · rw [mem_Ioo]
    exact ⟨neg_lt_zero.mpr hpos, by positivity⟩
  · apply Ioo_subset_Ioo <;> linarith

lemma eqOn_abs_add_one_of_isMIntegralCurveOn_Ioo [BoundarylessManifold I M]
    (hv : CMDiff 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M))) {x : M}
    (γ : ℝ → ℝ → M) (hγx : ∀ a, γ a 0 = x) (hγ : ∀ a > 0, IsMIntegralCurveOn (γ a) v (Ioo (-a) a))
    {a : ℝ} : EqOn (fun t ↦ γ (|t| + 1) t) (γ a) (Ioo (-a) a) := by
  intro t ht
  by_cases! hlt : |t| + 1 < a
  · exact eqOn_of_isMIntegralCurveOn_Ioo hv γ hγx hγ
      (by positivity) hlt.le (abs_lt.mp <| lt_add_one _)
  · exact eqOn_of_isMIntegralCurveOn_Ioo hv γ hγx hγ
      (neg_lt_self_iff.mp <| lt_trans ht.1 ht.2) hlt ht |>.symm

lemma isMIntegralCurve_abs_add_one_of_isMIntegralCurveOn_Ioo [BoundarylessManifold I M]
    (hv : CMDiff 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M))) {x : M}
    (γ : ℝ → ℝ → M) (hγx : ∀ a, γ a 0 = x) (hγ : ∀ a > 0, IsMIntegralCurveOn (γ a) v (Ioo (-a) a)) :
    IsMIntegralCurve (fun t ↦ γ (|t| + 1) t) v := by
  intro t
  have ht : t ∈ Ioo (-(|t| + 1)) (|t| + 1) := by
    rw [mem_Ioo, ← abs_lt]
    exact lt_add_one _
  apply HasMFDerivAt.congr_of_eventuallyEq (f := γ (|t| + 1))
  · exact hγ (|t| + 1) (by positivity) _ ht |>.hasMFDerivAt (Ioo_mem_nhds ht.1 ht.2)
  · rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Ioo (-(|t| + 1)) (|t| + 1), ?_,
      eqOn_abs_add_one_of_isMIntegralCurveOn_Ioo hv γ hγx hγ⟩
    have : |t| < |t| + 1 := lt_add_of_pos_right |t| zero_lt_one
    rw [abs_lt] at this
    exact Ioo_mem_nhds this.1 this.2

lemma exists_isMIntegralCurve_iff_exists_isMIntegralCurveOn_Ioo [BoundarylessManifold I M]
    (hv : CMDiff 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M))) (x : M) :
    (∃ γ, γ 0 = x ∧ IsMIntegralCurve γ v) ↔
      ∀ a, ∃ γ, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ioo (-a) a) := by
  refine ⟨fun ⟨γ, h1, h2⟩ _ ↦ ⟨γ, h1, h2.isMIntegralCurveOn _⟩, fun h ↦ ?_⟩
  choose γ hγx hγ using h
  exact ⟨fun t ↦ γ (|t| + 1) t, hγx (|0| + 1),
    isMIntegralCurve_abs_add_one_of_isMIntegralCurveOn_Ioo hv γ hγx (fun a _ ↦  hγ a)⟩

lemma eqOn_piecewise_of_isMIntegralCurveOn_Ioo [BoundarylessManifold I M]
    (hv : CMDiff 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    {a b a' b' : ℝ} (hγ : IsMIntegralCurveOn γ v (Ioo a b))
    (hγ' : IsMIntegralCurveOn γ' v (Ioo a' b'))
    (ht₀ : t₀ ∈ Ioo a b ∩ Ioo a' b') (h : γ t₀ = γ' t₀) :
    EqOn (piecewise (Ioo a b) γ γ') γ' (Ioo a' b') := by
  intro t ht
  suffices H : EqOn γ γ' (Ioo (max a a') (min b b')) by
    by_cases hmem : t ∈ Ioo a b
    · rw [piecewise, if_pos hmem]
      apply H
      simp [ht.1, ht.2, hmem.1, hmem.2]
    · rw [piecewise, if_neg hmem]
  apply isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless _ hv
    (hγ.mono (Ioo_subset_Ioo (le_max_left ..) (min_le_left ..)))
    (hγ'.mono (Ioo_subset_Ioo (le_max_right ..) (min_le_right ..))) h
  exact ⟨max_lt ht₀.1.1 ht₀.2.1, lt_min ht₀.1.2 ht₀.2.2⟩

lemma isMIntegralCurveOn_piecewise [BoundarylessManifold I M]
    (hv : CMDiff 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    {a b a' b' : ℝ} (hγ : IsMIntegralCurveOn γ v (Ioo a b))
    (hγ' : IsMIntegralCurveOn γ' v (Ioo a' b')) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo a b ∩ Ioo a' b') (h : γ t₀ = γ' t₀) :
    IsMIntegralCurveOn (piecewise (Ioo a b) γ γ') v (Ioo a b ∪ Ioo a' b') := by
  intro t ht
  by_cases hmem : t ∈ Ioo a b
  · rw [piecewise, if_pos hmem]
    apply hγ t hmem |>.hasMFDerivAt (Ioo_mem_nhds hmem.1 hmem.2) |>.hasMFDerivWithinAt
      (s := Ioo a b ∪ Ioo a' b') |>.congr_of_eventuallyEq _ (by rw [piecewise, if_pos hmem])
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Ioo a b, ?_, fun _ ht' ↦ by rw [piecewise, if_pos ht']⟩
    rw [(isOpen_Ioo.union isOpen_Ioo).nhdsWithin_eq ht]
    exact Ioo_mem_nhds hmem.1 hmem.2
  · have ht' := ht
    rw [mem_union, or_iff_not_imp_left] at ht
    rw [piecewise, if_neg hmem]
    apply hγ' t (ht hmem) |>.hasMFDerivAt (Ioo_mem_nhds (ht hmem).1 (ht hmem).2)
      |>.hasMFDerivWithinAt (s := Ioo a b ∪ Ioo a' b')
      |>.congr_of_eventuallyEq _ (by rw [piecewise, if_neg hmem])
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Ioo a' b', ?_,
      eqOn_piecewise_of_isMIntegralCurveOn_Ioo hv hγ hγ' ht₀ h⟩
    rw [(isOpen_Ioo.union isOpen_Ioo).nhdsWithin_eq ht']
    exact Ioo_mem_nhds (ht hmem).1 (ht hmem).2
