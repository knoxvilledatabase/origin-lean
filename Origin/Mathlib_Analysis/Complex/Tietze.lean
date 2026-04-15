/-
Extracted from Analysis/Complex/Tietze.lean
Genuine: 4 of 10 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core

/-!
# Finite-dimensional topological vector spaces over `ℝ` satisfy the Tietze extension property

There are two main results here:

- `RCLike.instTietzeExtensionTVS`: finite-dimensional topological vector spaces over `ℝ` (or `ℂ`)
  have the Tietze extension property.
- `BoundedContinuousFunction.exists_norm_eq_restrict_eq`: when mapping into a finite-dimensional
  normed vector space over `ℝ` (or `ℂ`), the extension can be chosen to preserve the norm of the
  bounded continuous function it extends.

-/

universe u u₁ v w

theorem TietzeExtension.of_tvs (𝕜 : Type v) [NontriviallyNormedField 𝕜] {E : Type w}
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜]
    [TietzeExtension.{u, v} 𝕜] : TietzeExtension.{u, w} E :=
  Module.Basis.ofVectorSpace 𝕜 E |>.equivFun.toContinuousLinearEquiv.toHomeomorph |> .of_homeo

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): Complex.instTietzeExtension

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): RCLike.instTietzeExtensionTVS

-- INSTANCE (free from Core): Set.instTietzeExtensionUnitBall

-- INSTANCE (free from Core): Set.instTietzeExtensionUnitClosedBall

theorem Metric.instTietzeExtensionBall {𝕜 : Type v} [RCLike 𝕜] {E : Type w}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] {r : ℝ} (hr : 0 < r) :
    TietzeExtension.{u, w} (Metric.ball (0 : E) r) :=
  have : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  .of_homeo <| show (Metric.ball (0 : E) r) ≃ₜ (Metric.ball (0 : E) 1) from
    OpenPartialHomeomorph.unitBallBall (0 : E) r hr |>.toHomeomorphSourceTarget.symm

theorem Metric.instTietzeExtensionClosedBall (𝕜 : Type v) [RCLike 𝕜] {E : Type w}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] (y : E) {r : ℝ} (hr : 0 < r) :
    TietzeExtension.{u, w} (Metric.closedBall y r) :=
  .of_homeo <| by
    change (Metric.closedBall y r) ≃ₜ (Metric.closedBall (0 : E) 1)
    symm
    apply (DilationEquiv.smulTorsor y (k := (r : 𝕜)) <| by exact_mod_cast hr.ne').toHomeomorph.sets
    ext x
    simp only [mem_closedBall, dist_zero_right, DilationEquiv.coe_toHomeomorph, Set.mem_preimage,
      DilationEquiv.smulTorsor_apply, vadd_eq_add, dist_add_self_left, norm_smul,
      RCLike.norm_ofReal, abs_of_nonneg hr.le]
    exact (mul_le_iff_le_one_right hr).symm

-- INSTANCE (free from Core): unitInterval.instTietzeExtension

variable {X : Type u} [TopologicalSpace X] [NormalSpace X] {s : Set X} (hs : IsClosed s)

variable (𝕜 : Type v) [RCLike 𝕜]

variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

namespace BoundedContinuousFunction

include 𝕜 hs in

theorem exists_norm_eq_restrict_eq (f : s →ᵇ E) :
    ∃ g : X →ᵇ E, ‖g‖ = ‖f‖ ∧ g.restrict s = f := by
  by_cases hf : ‖f‖ = 0; · exact ⟨0, by aesop⟩
  have := Metric.instTietzeExtensionClosedBall.{u, v} 𝕜 (0 : E) (by simp_all : 0 < ‖f‖)
  have hf' x : f x ∈ Metric.closedBall 0 ‖f‖ := by simpa using f.norm_coe_le_norm x
  obtain ⟨g, hg_mem, hg⟩ := (f : C(s, E)).exists_forall_mem_restrict_eq hs hf'
  simp only [Metric.mem_closedBall, dist_zero_right] at hg_mem
  let g' : X →ᵇ E := .ofNormedAddCommGroup g (map_continuous g) ‖f‖ hg_mem
  refine ⟨g', ?_, by ext x; congrm($(hg) x)⟩
  apply le_antisymm ((g'.norm_le <| by positivity).mpr hg_mem)
  refine (f.norm_le <| by positivity).mpr fun x ↦ ?_
  have hx : f x = g' x := by simpa using congr($(hg) x).symm
  rw [hx]
  exact g'.norm_le (norm_nonneg g') |>.mp le_rfl x

end BoundedContinuousFunction
