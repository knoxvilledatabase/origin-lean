/-
Extracted from Geometry/Manifold/Riemannian/PathELength.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Lengths of paths in manifolds

Consider a manifold in which the tangent spaces have an enormed structure. Then one defines
`pathELength γ a b` as the length of the path `γ : ℝ → M` between `a` and `b`, i.e., the integral
of the norm of its derivative on `Icc a b`.

We give several ways to write this quantity (as an integral over `Icc`, or `Ioo`, or the subtype
`Icc`, using either `mfderiv` or `mfderivWithin`).

We show that this notion is invariant under reparameterization by a monotone map, in
`pathELength_comp_of_monotoneOn`.

We define `riemannianEDist x y` as the infimum of the length of `C^1` paths between `x`
and `y`. We prove, in `exists_lt_locally_constant_of_riemannianEDist_lt`, that it is also the
infimum on such paths that are moreover locally constant near their endpoints. Such paths can be
glued while retaining the `C^1` property. We deduce that `riemannianEDist` satisfies the triangle
inequality, in `riemannianEDist_triangle`.

Note that `riemannianEDist x y` could also be named `finslerEDist x y` as we do not require that
the metric comes from an inner product space. However, as all the current applications in mathlib
are to Riemannian spaces we stick with the simpler name. This could be changed when Finsler
manifolds are studied in mathlib.
-/

open Set MeasureTheory

open scoped Manifold ENNReal ContDiff Topology

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

namespace Manifold

variable [∀ (x : M), ENorm (TangentSpace I x)] {a b c a' b' : ℝ} {γ γ' : ℝ → M}

variable (I) in

irreducible_def pathELength (γ : ℝ → M) (a b : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Icc a b, ‖mfderiv% γ t 1‖ₑ

lemma pathELength_eq_lintegral_mfderiv_Icc :
    pathELength I γ a b = ∫⁻ t in Icc a b, ‖mfderiv% γ t 1‖ₑ := by simp [pathELength]

lemma pathELength_eq_lintegral_mfderiv_Ioo :
    pathELength I γ a b = ∫⁻ t in Ioo a b, ‖mfderiv% γ t 1‖ₑ := by
  rw [pathELength_eq_lintegral_mfderiv_Icc, restrict_Ioo_eq_restrict_Icc]

lemma pathELength_eq_lintegral_mfderivWithin_Icc :
    pathELength I γ a b = ∫⁻ t in Icc a b, ‖mfderiv[Icc a b] γ t 1‖ₑ := by
  -- we use that the endpoints have measure 0 to rewrite on `Ioo a b`, where `mfderiv` and
  -- `mfderivWithin` coincide.
  rw [pathELength_eq_lintegral_mfderiv_Icc, ← restrict_Ioo_eq_restrict_Icc]
  apply setLIntegral_congr_fun measurableSet_Ioo (fun t ht ↦ ?_)
  rw [mfderivWithin_of_mem_nhds]
  exact Icc_mem_nhds ht.1 ht.2
