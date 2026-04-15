/-
Extracted from Analysis/Complex/Schwarz.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Schwarz lemma

In this file we prove several versions of the Schwarz lemma.

* `Complex.norm_deriv_le_div_of_mapsTo_ball`. Let `f : ℂ → E` be a complex analytic function
  on an open disk with center `c` and a positive radius `R₁`.
  If `f` sends this ball to a closed ball with center `f c` and radius `R₂`,
  then the norm of the derivative of `f` at `c` is at most the ratio `R₂ / R₁`.

* `Complex.dist_le_div_mul_dist_of_mapsTo_ball`. Let `f : E → F` be a complex analytic function
  on an open ball with center `c` and radius `R₁`.
  If `f` sends this ball to a closed ball with center `f c` and radius `R₂`,
  then for any `z` in the former ball we have `dist (f z) (f c) ≤ (R₂ / R₁) * dist z c`.

* `Complex.norm_deriv_le_one_of_mapsTo_ball`. If `f : ℂ → E` is complex analytic
  on an open disk with center `c` and a positive radius `R₁`,
  and it sends this disk to a closed ball with center `f c` and radius the same radius,
  then the norm of the derivative of `f` at the center of this disk is at most `1`.

* `Complex.dist_le_dist_of_mapsTo_ball`. Let `f : E → F` be a complex analytic function
  on an open ball with center `c`.
  If `f` sends this ball to a closed ball with center `f c` and the same radius,
  then for any `z` in the former ball we have `dist (f z) (f c) ≤ dist z c`.

* `Complex.norm_le_norm_of_mapsTo_ball`:
  Let `f : E → F` be a complex analytic on an open ball with center at the origin.
  If `f` sends this ball to the closed ball with center `0` of the same radius and `f 0 = 0`,
  then for any point `z` of this disk we have `‖f z‖ ≤ ‖z‖`.

## Implementation notes

Traditionally, the Schwarz lemma is formulated for maps `f : ℂ → ℂ`.
We generalize all versions of the lemma to the case of maps to any normed space.
For the versions that don't use `deriv` or `dslope`,
we state it for maps between any two normed spaces.

## TODO

* Prove that any diffeomorphism of the unit disk to itself is a Möbius map.

## Tags

Schwarz lemma
-/

open Metric Set Function Filter TopologicalSpace

open scoped Topology ComplexConjugate

namespace Complex

theorem schwarz_aux {f : ℂ → ℂ} {c z : ℂ} {R₁ R₂ : ℝ} {n : ℕ}
    (hd : DifferentiableOn ℂ f (ball c R₁)) (h_maps : MapsTo f (ball c R₁) (closedBall (f c) R₂))
    (hn : (f · - f c) =o[𝓝 c] (fun w ↦ (w - c) ^ n)) (hz : z ∈ ball c R₁) :
    ‖f z - f c‖ ≤ R₂ * (‖z - c‖ / R₁) ^ (n + 1) := by
  -- By slightly reducing `R₁`, we can assume that `f` is differentiable on `closedBall c R₁`
  -- and it maps this ball to the closed ball in the codomain.
  have hR₁ : 0 < R₁ := nonempty_ball.1 ⟨z, hz⟩
  wlog hd' : DifferentiableOn ℂ f (closedBall c R₁) ∧
    MapsTo f (closedBall c R₁) (closedBall (f c) R₂) generalizing R₁
  · suffices ∀ᶠ r in 𝓝[<] R₁, ‖f z - f c‖ ≤ R₂ * (‖z - c‖ / r) ^ (n + 1) by
      refine ge_of_tendsto ?_ this
      refine ContinuousAt.continuousWithinAt ?_
      fun_prop (disch := positivity)
    rw [mem_ball_iff_norm] at hz
    filter_upwards [Ioo_mem_nhdsLT hz] with r ⟨hzr, hrR₁⟩
    apply this
    · exact hd.mono <| by gcongr
    · exact h_maps.mono_left <| by gcongr
    · rwa [mem_ball_iff_norm]
    · exact (norm_nonneg _).trans_lt hzr
    · exact ⟨hd.mono <| closedBall_subset_ball hrR₁, h_maps.mono_left <|
        closedBall_subset_ball hrR₁⟩
  -- Cleanup, discard the case `z = c`.
  clear hd h_maps
  rcases hd' with ⟨hd, h_maps⟩
  rcases eq_or_ne z c with rfl | hne
  · simp
  -- Consider the function given by `g w := ((w - c) ^ (n + 1))⁻¹ * (f w - f c)`.
  -- It is differentiable away from `c` and satisfies `g w = o((w - c)⁻¹)`,
  -- thus it can be extended to a function g'` differentiable on the whole closed ball
  -- with center c` and radius `R₁`.
  set g : ℂ → ℂ := fun w ↦ ((w - c) ^ (n + 1))⁻¹ * (f w - f c)
  set g' := update g c (limUnder (𝓝[≠] c) g)
  have hdg' : DifferentiableOn ℂ g' (closedBall c R₁) := by
    refine .mono ?_ (subset_insert_diff_singleton c _)
    apply differentiableOn_update_limUnder_insert_of_isLittleO
    · exact diff_mem_nhdsWithin_compl (closedBall_mem_nhds _ hR₁) _
    · refine .mul ?_ (hd.mono diff_subset |>.sub_const _)
      fun_prop (disch := simp +contextual [sub_eq_zero])
    · refine Asymptotics.isBigO_refl (fun w ↦ ((w - c) ^ (n + 1))⁻¹) _ |>.mul_isLittleO hn
        |>.mono (nhdsWithin_le_nhds (s := {c}ᶜ)) |>.congr' ?_ ?_
      · simp [g]
      · refine eventually_mem_nhdsWithin.mono fun w hw ↦ ?_
        rw [mem_compl_singleton_iff, ← sub_ne_zero] at hw
        simp [pow_succ, field]
  -- Finally, we apply the maximum modulus principle to this function.
  -- On the sphere `dist w c = R₁`, its norm is bounded by `R₂ / R₁ ^ (n + 1)`,
  -- thus it's bounded by the same constant on the whole closed ball,
  -- in particular, at `w = z`.
  suffices ‖g' z‖ ≤ R₂ / R₁ ^ (n + 1) by
    have hz' : ‖z - c‖ ≠ 0 := by simpa [sub_eq_zero] using hne
    simpa [g', hne, g, div_pow, mul_comm, field] using this
  refine norm_le_of_forall_mem_frontier_norm_le isBounded_ball (hdg'.diffContOnCl_ball subset_rfl)
    ?_ ?_
  · grw [frontier_ball_subset_sphere]
    intro w hw
    have hwc := ne_of_mem_sphere hw hR₁.ne'
    have hfw : ‖f w - f c‖ ≤ R₂ := by
      simpa [dist_eq_norm] using h_maps (sphere_subset_closedBall hw)
    rw [mem_sphere_iff_norm] at hw
    simpa [g', hwc, g, hw, field]
  · exact subset_closure hz

section NormedSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
  {R R₁ R₂ : ℝ} {f : E → F} {c z : E}

open AffineMap in

theorem dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO {f : E → F} {c z : E} {R₁ R₂ : ℝ} {n : ℕ}
    (hd : DifferentiableOn ℂ f (ball c R₁)) (h_maps : MapsTo f (ball c R₁) (closedBall (f c) R₂))
    (hn : (f · - f c) =o[𝓝 c] (fun w ↦ ‖w - c‖ ^ n)) (hz : z ∈ ball c R₁) :
    dist (f z) (f c) ≤ R₂ * (dist z c / R₁) ^ (n + 1) := by
  -- Note that `0 < R₁`, `0 ≤ R₂`, then discard the trivial case `f z = f c`.
  have hR₁ : 0 < R₁ := nonempty_ball.mp ⟨_, hz⟩
  have hR₂ : 0 ≤ R₂ := nonempty_closedBall.mp ⟨_, h_maps hz⟩
  rcases eq_or_ne (f z) (f c) with heq | hfne
  · trans 0 <;> [simp [heq]; positivity]
  have hne : z ≠ c := ne_of_apply_ne _ hfne
  -- Let `g : F → ℂ` be a continuous linear function such that `‖g‖ = 1`
  -- and `‖g (f z - f c)‖ = ‖f z - f c‖`.
  rcases exists_dual_vector ℂ _ (norm_sub_eq_zero_iff.not.mpr hfne) with ⟨g, hg, hgf⟩
  -- Consider `h : ℂ → ℂ` given by `h w = g (f (c + w * (z - c)))`.
  set h : ℂ → ℂ := g ∘ f ∘ lineMap c z
  -- This map is differentiable on the ball with center at the origin and radius `R₁ / dist z c`
  -- and it sends this ball to the closed ball with center `h 0 = f c` and radius R₂`.
  have hmaps_line : MapsTo (lineMap c z) (ball (0 : ℂ) (R₁ / dist z c)) (ball c R₁) := by
    intro w hw
    simpa [lt_div_iff₀, hne, dist_comm c] using hw
  have hmaps : MapsTo h (ball 0 (R₁ / dist z c)) (closedBall (h 0) R₂) := by
    refine MapsTo.comp ?_ (h_maps.comp hmaps_line)
    simpa [hg, h] using g.lipschitz.mapsTo_closedBall (f c) R₂
  have hdiff : DifferentiableOn ℂ h (ball 0 (R₁ / dist z c)) :=
    g.differentiable.comp_differentiableOn <| hd.comp (lineMap c z).differentiableOn hmaps_line
  -- This map also satisfies `h(w) - h(0) = o(w ^ n)`, thus we can apply the auxiliary lemma above.
  have hn : (h · - h 0) =o[𝓝 0] (fun w ↦ (w - 0) ^ n) := by
    simp only [h, ← map_sub, Function.comp_apply, sub_zero]
    refine (g.isBigO_comp _ _).trans_isLittleO ?_
    rw [← lineMap_apply_zero (k := ℂ) c z] at hn
    refine hn.comp_tendsto ?_ |>.trans_isBigO ?_
    · exact Continuous.tendsto (by fun_prop) 0
    · simpa [Function.comp_def, ← dist_eq_norm_sub, mul_pow, mul_comm]
        using (Asymptotics.isBigO_refl (· ^ n) (𝓝 (0 : ℂ))).norm_left.const_mul_left _
  have hmem : 1 ∈ ball (0 : ℂ) (R₁ / dist z c) := by
    simpa [lt_div_iff₀, hne]
  rw [map_sub] at hgf
  simpa [hgf, h, dist_eq_norm_sub] using schwarz_aux hdiff hmaps hn hmem

theorem dist_le_div_mul_dist_of_mapsTo_ball (hd : DifferentiableOn ℂ f (ball c R₁))
    (h_maps : MapsTo f (ball c R₁) (closedBall (f c) R₂)) (hz : z ∈ ball c R₁) :
    dist (f z) (f c) ≤ R₂ / R₁ * dist z c := by
  refine dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO (n := 0) hd h_maps ?_ hz |>.trans_eq ?_
  · simpa using hd.continuousOn.continuousAt
      (ball_mem_nhds _ <| nonempty_ball.mp ⟨_, hz⟩) |>.sub_const (f c)
  · simp [field]

theorem norm_fderiv_le_div_of_mapsTo_ball (hd : DifferentiableOn ℂ f (ball c R₁))
    (h_maps : MapsTo f (ball c R₁) (closedBall (f c) R₂)) (h₀ : 0 < R₁) :
    ‖fderiv ℂ f c‖ ≤ R₂ / R₁ := by
  have : 0 ≤ R₂ := nonempty_closedBall.mp <| h_maps.nonempty <| nonempty_ball.mpr h₀
  refine norm_fderiv_le_of_lip' _ (by positivity) ?_
  filter_upwards [ball_mem_nhds _ h₀] with z hz
  simpa [dist_eq_norm_sub] using dist_le_div_mul_dist_of_mapsTo_ball hd h_maps hz

theorem dist_le_dist_of_mapsTo_ball (hd : DifferentiableOn ℂ f (ball c R))
    (h_maps : MapsTo f (ball c R) (closedBall (f c) R)) (hz : z ∈ ball c R) :
    dist (f z) (f c) ≤ dist z c := by
  simpa [(nonempty_ball.1 ⟨z, hz⟩).ne'] using dist_le_div_mul_dist_of_mapsTo_ball hd h_maps hz
