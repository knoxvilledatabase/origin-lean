/-
Extracted from Topology/VectorBundle/Riemannian.lean
Genuine: 9 of 11 | Dissolved: 1 | Infrastructure: 1
-/
import Origin.Core

/-! # Riemannian vector bundles

Given a real vector bundle over a topological space whose fibers are all endowed with an inner
product, we say that this bundle is Riemannian if the inner product depends continuously on the
base point.

We introduce a typeclass `[IsContinuousRiemannianBundle F E]` registering this property.
Under this assumption, we show that the inner product of two continuous maps into the same fibers
of the bundle is a continuous function.

If one wants to endow an existing vector bundle with a Riemannian metric, there is a subtlety:
the inner product space structure on the fibers should give rise to a topology on the fibers
which is defeq to the original one, to avoid diamonds. To do this, we introduce a
class `[RiemannianBundle E]` containing the data of an inner
product on the fibers defining the same topology as the original one. Given this class, we can
construct `NormedAddCommGroup` and `InnerProductSpace` instances on the fibers, compatible in a
defeq way with the initial topology. If the data used to register the instance `RiemannianBundle E`
depends continuously on the base point, we register automatically an instance of
`[IsContinuousRiemannianBundle F E]` (and similarly if the data is smooth).

The general theory should be built assuming `[IsContinuousRiemannianBundle F E]`, while the
`[RiemannianBundle E]` mechanism is only to build data in specific situations, for instance for
the tangent bundle. As instances related to Riemannian bundles are both costly and quite specific,
they are scoped to the `Bundle` namespace.

## Keywords
Vector bundle, Riemannian metric
-/

open Bundle ContinuousLinearMap Filter

open scoped Topology

variable
  {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable (F E) in

class IsContinuousRiemannianBundle : Prop where
  /-- There exists a bilinear form, depending continuously on the basepoint and defining the
  inner product in the fibers. This is expressed as an existence statement so that it is Prop-valued
  in terms of existing data, the inner product on the fibers and the fiber bundle structure. -/
  exists_continuous : ∃ g : (Π x, E x →L[ℝ] E x →L[ℝ] ℝ),
    Continuous (fun (x : B) ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (g x))
    ∧ ∀ (x : B) (v w : E x), ⟪v, w⟫ = g x v w

section Trivial

variable {F₁ : Type*} [NormedAddCommGroup F₁] [InnerProductSpace ℝ F₁]

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): :

end Trivial

section Continuous

variable
  {M : Type*} [TopologicalSpace M] [h : IsContinuousRiemannianBundle F E]
  {b : M → B} {v w : ∀ x, E (b x)} {s : Set M} {x : M}

lemma ContinuousWithinAt.inner_bundle
    (hv : ContinuousWithinAt (fun m ↦ (v m : TotalSpace F E)) s x)
    (hw : ContinuousWithinAt (fun m ↦ (w m : TotalSpace F E)) s x) :
    ContinuousWithinAt (fun m ↦ ⟪v m, w m⟫) s x := by
  rcases h.exists_continuous with ⟨g, g_cont, hg⟩
  have hf : ContinuousWithinAt b s x := by
    simp only [FiberBundle.continuousWithinAt_totalSpace] at hv
    exact hv.1
  simp only [hg]
  have : ContinuousWithinAt
      (fun m ↦ TotalSpace.mk' ℝ (E := Bundle.Trivial B ℝ) (b m) (g (b m) (v m) (w m))) s x :=
    (g_cont.continuousAt.comp_continuousWithinAt hf).clm_bundle_apply₂ (F₁ := F) (F₂ := F) hv hw
  simp only [FiberBundle.continuousWithinAt_totalSpace] at this
  exact this.2

lemma ContinuousAt.inner_bundle
    (hv : ContinuousAt (fun m ↦ (v m : TotalSpace F E)) x)
    (hw : ContinuousAt (fun m ↦ (w m : TotalSpace F E)) x) :
    ContinuousAt (fun b ↦ ⟪v b, w b⟫) x := by
  simp only [← continuousWithinAt_univ] at hv hw ⊢
  exact ContinuousWithinAt.inner_bundle hv hw

lemma ContinuousOn.inner_bundle
    (hv : ContinuousOn (fun m ↦ (v m : TotalSpace F E)) s)
    (hw : ContinuousOn (fun m ↦ (w m : TotalSpace F E)) s) :
    ContinuousOn (fun b ↦ ⟪v b, w b⟫) s :=
  fun x hx ↦ (hv x hx).inner_bundle (hw x hx)

lemma Continuous.inner_bundle
    (hv : Continuous (fun m ↦ (v m : TotalSpace F E)))
    (hw : Continuous (fun m ↦ (w m : TotalSpace F E))) :
    Continuous (fun b ↦ ⟪v b, w b⟫) := by
  simp only [continuous_iff_continuousAt] at hv hw ⊢
  exact fun x ↦ (hv x).inner_bundle (hw x)

variable (F E)

lemma eventually_norm_symmL_trivializationAt_self_comp_lt (x : B) {r : ℝ} (hr : 1 < r) :
    ∀ᶠ y in 𝓝 x, ‖((trivializationAt F E x).symmL ℝ x)
      ∘L ((trivializationAt F E x).continuousLinearMapAt ℝ y)‖ < r := by
  /- We will expand the definition of continuity of the inner product structure, in the chart.
  Denote `g' x` the metric in the fiber of `x`, read in the chart. For `y` close to `x`, then
  `g' y` and `g' x` are close. The inequality we have to prove reduces to comparing
  `g' y w w` and `g' x w w`, where `w` is the image in the chart of a tangent vector `v` at `y`.
  Their difference is controlled by `δ ‖w‖ ^ 2` for any small `δ > 0`. To conclude, we argue that
  `‖w‖` is comparable to the norm inside the fiber over `x`, i.e., `g' x w w`, because there
  is a continuous linear equivalence between these two spaces by definition of vector bundles. -/
  obtain ⟨r', hr', r'r⟩ : ∃ r', 1 < r' ∧ r' < r := exists_between hr
  have h'x : x ∈ (trivializationAt F E x).baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  let G := (trivializationAt F E x).continuousLinearEquivAt ℝ x h'x
  let C := (‖(G : E x →L[ℝ] F)‖) ^ 2
  -- choose `δ` small enough that the computation below works when the metrics at `x` and `y`
  -- are `δ` close. When writing this proof, I have followed my nose in the computation, and
  -- recorded only in the end how small `δ` needs to be. The reader should skip the precise
  -- condition for now, as it doesn't give any useful insight.
  obtain ⟨δ, δpos, hδ⟩ : ∃ δ, 0 < δ ∧ (r' ^ 2)⁻¹ < 1 - δ * C := by
    have A : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
    have B : Tendsto (fun δ ↦ 1 - δ * C) (𝓝[>] 0) (𝓝 (1 - 0 * C)) := by
      apply tendsto_inf_left
      exact tendsto_const_nhds.sub (tendsto_id.mul tendsto_const_nhds)
    have B' : ∀ᶠ δ in 𝓝[>] 0, (r' ^ 2)⁻¹ < 1 - δ * C := by
      apply (tendsto_order.1 B).1
      simpa using inv_lt_one_of_one_lt₀ (by nlinarith)
    exact (A.and B').exists
  rcases h.exists_continuous with ⟨g, g_cont, hg⟩
  let g' : B → F →L[ℝ] F →L[ℝ] ℝ := fun y ↦
    inCoordinates F E (F →L[ℝ] ℝ) (fun x ↦ E x →L[ℝ] ℝ) x y x y (g y)
  have hg' : ContinuousAt g' x := by
    have W := g_cont.continuousAt (x := x)
    simp only [continuousAt_hom_bundle] at W
    exact W.2
  have : ∀ᶠ y in 𝓝 x, dist (g' y) (g' x) < δ := by
    rw [Metric.continuousAt_iff'] at hg'
    apply hg' _ δpos
  filter_upwards [this, (trivializationAt F E x).open_baseSet.mem_nhds h'x] with y hy h'y
  have : ‖g' x - g' y‖ ≤ δ := by rw [← dist_eq_norm']; exact hy.le
  -- To show that the norm of the composition is bounded by `r'`, we start from a vector
  -- `‖v‖`. We will show that its image has a controlled norm.
  apply (opNorm_le_bound _ (by linarith) (fun v ↦ ?_)).trans_lt r'r
  -- rewrite the norm of `‖v‖` and of its image in terms of norms in the model space
  let w := (trivializationAt F E x).continuousLinearMapAt ℝ y v
  suffices ‖((trivializationAt F E x).symmL ℝ x) w‖ ^ 2 ≤ r' ^ 2 * ‖v‖ ^ 2 from
    le_of_sq_le_sq (by simpa [mul_pow]) (by positivity)
  simp only [Trivialization.symmL_apply, ← real_inner_self_eq_norm_sq, hg]
  have hgy : g y v v = g' y w w := by
    rw [inCoordinates_apply_eq₂ h'y h'y (Set.mem_univ _)]
    have A : ((trivializationAt F E x).symm y)
       ((trivializationAt F E x).linearMapAt ℝ y v) = v := by
      convert ((trivializationAt F E x).continuousLinearEquivAt ℝ _ h'y).symm_apply_apply v
      simp [Trivialization.coe_continuousLinearEquivAt_eq _ h'y]
    simp [A, w]
  have hgx : g x ((trivializationAt F E x).symm x w) ((trivializationAt F E x).symm x w) =
      g' x w w := by
    rw [inCoordinates_apply_eq₂ h'x h'x (Set.mem_univ _)]
    simp
  rw [hgx, hgy]
  -- get a good control for the norms of `w` in the model space, using continuity
  have : g' x w w ≤ δ * C * g' x w w + g' y w w := calc
        g' x w w
    _ = (g' x - g' y) w w + g' y w w := by simp
    _ ≤ ‖g' x - g' y‖ * ‖w‖ * ‖w‖ + g' y w w := by
      grw [← le_opNorm₂, ← Real.le_norm_self]
    _ ≤ δ * ‖w‖ ^ 2 + g' y w w := by
      rw [pow_two, mul_assoc]; gcongr
    _ ≤ δ * (‖(G : E x →L[ℝ] F)‖ * ‖G.symm w‖) ^ 2 + g' y w w := by
      grw [← le_opNorm]
      simp
    _ = δ * C * ‖G.symm w‖ ^ 2 + g' y w w := by ring
    _ = δ * C * g x (G.symm w) (G.symm w) + g' y w w := by simp [← hg]
    _ = δ * C * g' x w w + g' y w w := by
      rw [← hgx]; rfl
  have : (1 - δ * C) * g' x w w ≤ g' y w w := by linarith
  rw [← (le_div_iff₀' (lt_of_le_of_lt (by positivity) hδ)), div_eq_inv_mul] at this
  grw [this]
  gcongr
  · rw [← hgy, ← hg, real_inner_self_eq_norm_sq]
    positivity
  · exact inv_le_of_inv_le₀ (by positivity) hδ.le

lemma eventually_norm_trivializationAt_lt (x : B) :
    ∃ C > 0, ∀ᶠ y in 𝓝 x, ‖(trivializationAt F E x).continuousLinearMapAt ℝ y‖ < C := by
  refine ⟨(1 + ‖(trivializationAt F E x).continuousLinearMapAt ℝ  x‖) * 2, by positivity, ?_⟩
  filter_upwards [eventually_norm_symmL_trivializationAt_self_comp_lt F E x one_lt_two] with y hy
  have A : ((trivializationAt F E x).continuousLinearMapAt ℝ x) ∘L
      ((trivializationAt F E x).symmL ℝ x) = ContinuousLinearMap.id _ _ := by
    ext v
    have h'x : x ∈ (trivializationAt F E x).baseSet := FiberBundle.mem_baseSet_trivializationAt' x
    simp only [coe_comp', Trivialization.continuousLinearMapAt_apply, Trivialization.symmL_apply,
      Function.comp_apply, coe_id', id_eq]
    convert ((trivializationAt F E x).continuousLinearEquivAt ℝ _ h'x).apply_symm_apply v
    simp [Trivialization.coe_continuousLinearEquivAt_eq _ h'x]
  have : (trivializationAt F E x).continuousLinearMapAt ℝ y =
    (ContinuousLinearMap.id _ _) ∘L ((trivializationAt F E x).continuousLinearMapAt ℝ y) := by simp
  grw [this, ← A, comp_assoc, opNorm_comp_le]
  gcongr
  linarith

lemma eventually_norm_symmL_trivializationAt_comp_self_lt (x : B) {r : ℝ} (hr : 1 < r) :
    ∀ᶠ y in 𝓝 x, ‖((trivializationAt F E x).symmL ℝ y)
      ∘L ((trivializationAt F E x).continuousLinearMapAt ℝ x)‖ < r := by
  /- We will expand the definition of continuity of the inner product structure, in the chart.
  Denote `g' x` the metric in the fiber of `x`, read in the chart. For `y` close to `x`, then
  `g' y` and `g' x` are close. The inequality we have to prove reduces to comparing
  `g' y w w` and `g' x w w`, where `w` is the image in the chart of a tangent vector `v` at `x`.
  Their difference is controlled by `δ ‖w‖ ^ 2` for any small `δ > 0`. To conclude, we argue that
  `‖w‖` is comparable to the norm inside the fiber over `x`, i.e., `g' x w w`, because there
  is a continuous linear equivalence between these two spaces by definition of vector bundles. -/
  obtain ⟨r', hr', r'r⟩ : ∃ r', 1 < r' ∧ r' < r := exists_between hr
  have h'x : x ∈ (trivializationAt F E x).baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  let G := (trivializationAt F E x).continuousLinearEquivAt ℝ x h'x
  let C := (‖(G : E x →L[ℝ] F)‖) ^ 2
  -- choose `δ` small enough that the computation below works when the metrics at `x` and `y`
  -- are `δ` close. When writing this proof, I have followed my nose in the computation, and
  -- recorded only in the end how small `δ` needs to be. The reader should skip the precise
  -- condition for now, as it doesn't give any useful insight.
  obtain ⟨δ, δpos, h'δ⟩ : ∃ δ, 0 < δ ∧ (1 + δ * C) < r' ^ 2 := by
    have A : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
    have B : Tendsto (fun δ ↦ 1 + δ * C) (𝓝[>] 0) (𝓝 (1 + 0 * C)) := by
      apply tendsto_inf_left
      exact tendsto_const_nhds.add (tendsto_id.mul tendsto_const_nhds)
    have B' : ∀ᶠ δ in 𝓝[>] 0, 1 + δ * C < r' ^ 2 := by
      apply (tendsto_order.1 B).2
      simpa using hr'.trans_le (le_abs_self _)
    exact (A.and B').exists
  rcases h.exists_continuous with ⟨g, g_cont, hg⟩
  let g' : B → F →L[ℝ] F →L[ℝ] ℝ := fun y ↦
    inCoordinates F E (F →L[ℝ] ℝ) (fun x ↦ E x →L[ℝ] ℝ) x y x y (g y)
  have hg' : ContinuousAt g' x := by
    have W := g_cont.continuousAt (x := x)
    simp only [continuousAt_hom_bundle] at W
    exact W.2
  have : ∀ᶠ y in 𝓝 x, dist (g' y) (g' x) < δ := by
    rw [Metric.continuousAt_iff'] at hg'
    apply hg' _ δpos
  filter_upwards [this, (trivializationAt F E x).open_baseSet.mem_nhds h'x] with y hy h'y
  have : ‖g' y - g' x‖ ≤ δ := by rw [← dist_eq_norm]; exact hy.le
  -- To show that the norm of the composition is bounded by `r'`, we start from a vector
  -- `‖v‖`. We will show that its image has a controlled norm.
  apply (opNorm_le_bound _ (by linarith) (fun v ↦ ?_)).trans_lt r'r
  -- rewrite the norm of `‖v‖` and of its image in terms of norms in the model space
  let w := (trivializationAt F E x).continuousLinearMapAt ℝ x v
  suffices ‖((trivializationAt F E x).symmL ℝ y) w‖ ^ 2 ≤ r' ^ 2 * ‖v‖ ^ 2 from
    le_of_sq_le_sq (by simpa [mul_pow]) (by positivity)
  simp only [Trivialization.symmL_apply, ← real_inner_self_eq_norm_sq, hg]
  have hgx : g x v v = g' x w w := by
    rw [inCoordinates_apply_eq₂ h'x h'x (Set.mem_univ _)]
    have A : ((trivializationAt F E x).symm x)
       ((trivializationAt F E x).linearMapAt ℝ x v) = v := by
      convert ((trivializationAt F E x).continuousLinearEquivAt ℝ _ h'x).symm_apply_apply v
      simp [Trivialization.coe_continuousLinearEquivAt_eq _ h'x]
    simp [A, w]
  have hgy : g y ((trivializationAt F E x).symm y w) ((trivializationAt F E x).symm y w)
      = g' y w w := by
    rw [inCoordinates_apply_eq₂ h'y h'y (Set.mem_univ _)]
    simp
  rw [hgx, hgy]
  -- get a good control for the norms of `w` in the model space, using continuity
  calc g' y w w
    _ = (g' y - g' x) w w + g' x w w := by simp
    _ ≤ ‖g' y - g' x‖ * ‖w‖ * ‖w‖ + g' x w w := by
      grw [← le_opNorm₂, ← Real.le_norm_self]
    _ ≤ δ * ‖w‖ ^ 2 + g' x w w := by
      rw [pow_two, mul_assoc]; gcongr
    _ ≤ δ * (‖(G : E x →L[ℝ] F)‖ * ‖G.symm w‖) ^ 2 + g' x w w := by
      grw [← le_opNorm]
      simp
    _ = δ * C * ‖G.symm w‖ ^ 2 + g' x w w := by ring
    _ = δ * C * g x (G.symm w) (G.symm w) + g' x w w := by simp [← hg]
    _ = δ * C * g' x w w + g' x w w := by
      congr
      rw [inCoordinates_apply_eq₂ h'x h'x (Set.mem_univ _)]
      simp only [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization,
        LinearMap.id_coe, id_eq, w]
      rfl
    _ = (1 + δ * C) * g' x w w := by ring
    _ ≤ r' ^ 2 * g' x w w := by
      gcongr
      rw [← hgx, ← hg, real_inner_self_eq_norm_sq]
      positivity

lemma eventually_norm_symmL_trivializationAt_lt (x : B) :
    ∃ C > 0, ∀ᶠ y in 𝓝 x, ‖(trivializationAt F E x).symmL ℝ y‖ < C := by
  refine ⟨2 * (1 + ‖(trivializationAt F E x).symmL ℝ x‖), by positivity, ?_⟩
  filter_upwards [eventually_norm_symmL_trivializationAt_comp_self_lt F E x one_lt_two] with y hy
  have A : ((trivializationAt F E x).continuousLinearMapAt ℝ x) ∘L
      ((trivializationAt F E x).symmL ℝ x) = ContinuousLinearMap.id _ _ := by
    ext v
    have h'x : x ∈ (trivializationAt F E x).baseSet := FiberBundle.mem_baseSet_trivializationAt' x
    simp only [coe_comp', Trivialization.continuousLinearMapAt_apply, Trivialization.symmL_apply,
      Function.comp_apply, coe_id', id_eq]
    convert ((trivializationAt F E x).continuousLinearEquivAt ℝ _ h'x).apply_symm_apply v
    simp [Trivialization.coe_continuousLinearEquivAt_eq _ h'x]
  have : (trivializationAt F E x).symmL ℝ y =
     ((trivializationAt F E x).symmL ℝ y) ∘L (ContinuousLinearMap.id _ _) := by simp
  grw [this, ← A, ← comp_assoc, opNorm_comp_le]
  gcongr
  linarith

end Continuous

namespace Bundle

section Construction

variable
  {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousConstSMul ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]

open Bornology

variable (E) in

-- DISSOLVED: RiemannianMetric
