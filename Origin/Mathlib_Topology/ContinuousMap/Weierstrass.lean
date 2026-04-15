/-
Extracted from Topology/ContinuousMap/Weierstrass.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The Weierstrass approximation theorem for continuous functions on `[a,b]`

We've already proved the Weierstrass approximation theorem
in the sense that we've shown that the Bernstein approximations
to a continuous function on `[0,1]` converge uniformly.

Here we rephrase this more abstractly as
`polynomialFunctions_closure_eq_top' : (polynomialFunctions I).topologicalClosure = ⊤`
and then, by precomposing with suitable affine functions,
`polynomialFunctions_closure_eq_top : (polynomialFunctions (Set.Icc a b)).topologicalClosure = ⊤`
-/

open ContinuousMap Filter

open scoped unitInterval

theorem polynomialFunctions_closure_eq_top' : (polynomialFunctions I).topologicalClosure = ⊤ := by
  apply top_unique
  rintro f -
  refine mem_closure_of_tendsto (bernsteinApproximation_uniform f) <| .of_forall fun n ↦ ?_
  apply Subalgebra.sum_mem
  rintro i -
  rw [← SetLike.mem_coe, polynomialFunctions_coe]
  use bernsteinPolynomial ℝ n i * .C (f (bernstein.z i))
  ext
  simp [bernstein]

theorem continuousMap_mem_polynomialFunctions_closure (a b : ℝ) (f : C(Set.Icc a b, ℝ)) :
    f ∈ (polynomialFunctions (Set.Icc a b)).topologicalClosure := by
  rw [polynomialFunctions_closure_eq_top _ _]
  simp

open scoped Polynomial

theorem exists_polynomial_near_continuousMap (a b : ℝ) (f : C(Set.Icc a b, ℝ)) (ε : ℝ)
    (pos : 0 < ε) : ∃ p : ℝ[X], ‖p.toContinuousMapOn _ - f‖ < ε := by
  have w := mem_closure_iff_frequently.mp (continuousMap_mem_polynomialFunctions_closure _ _ f)
  rw [Metric.nhds_basis_ball.frequently_iff] at w
  obtain ⟨-, H, ⟨m, ⟨-, rfl⟩⟩⟩ := w ε pos
  rw [Metric.mem_ball, dist_eq_norm] at H
  exact ⟨m, H⟩

theorem exists_polynomial_near_of_continuousOn (a b : ℝ) (f : ℝ → ℝ)
    (c : ContinuousOn f (Set.Icc a b)) (ε : ℝ) (pos : 0 < ε) :
    ∃ p : ℝ[X], ∀ x ∈ Set.Icc a b, |p.eval x - f x| < ε := by
  let f' : C(Set.Icc a b, ℝ) := ⟨fun x => f x, continuousOn_iff_continuous_restrict.mp c⟩
  obtain ⟨p, b⟩ := exists_polynomial_near_continuousMap a b f' ε pos
  use p
  rw [norm_lt_iff _ pos] at b
  intro x m
  exact b ⟨x, m⟩
