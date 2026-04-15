/-
Extracted from Analysis/Convex/MetricSpace.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Convex metric spaces

A convex metric space is a convex space with a compatible metric structure.
Concretely, we ask for `dist(∑ tᵢ xᵢ, ∑ tᵢ yᵢ) ≤ ∑ tᵢ dist(xᵢ, yᵢ)`,
which is what one would expect from the triangle inequality.

## Main results
- `IsConvexMetricSpace`: The (`Prop`-valued) class of convex metric spaces.
- `continuous_convexComboPair`: Binary convex combination is continuous.
- `Convex.isConvexMetricSpace`: Convex subspaces of normed spaces are convex metric spaces.

## TODO
- Equip `StdSimplex` with a topology and show the analogous continuity result for n-ary
  convex combinations.
- Tidy up the imports with `Mathlib.LinearAlgebra.ConvexSpace.AffineSpace` etc once those files
  are moved to proper places.

-/

open ConvexSpace

variable {X : Type*} [ConvexSpace ℝ X] [MetricSpace X]

variable (X) in

class IsConvexMetricSpace : Prop where
  /-- Use `dist_convexCombination_map_le` instead. -/
  dist_convexCombination_map_le' (f : StdSimplex ℝ ℕ) (x y : ℕ → X) :
    dist (convexCombination (f.map x)) (convexCombination (f.map y)) ≤
      f.weights.sum fun i r ↦ r * dist (x i) (y i)

variable [IsConvexMetricSpace X]

lemma dist_convexCombination_map_le {ι : Type*} (f : StdSimplex ℝ ι) (x y : ι → X) :
    dist (convexCombination (f.map x)) (convexCombination (f.map y)) ≤
      f.weights.sum fun i r ↦ r * dist (x i) (y i) := by
  classical
  let e : ι → ℕ := Function.extend (↑) (f.support.equivFin ·) 0
  have he (x : _) (hx : x ∈ f.support) : e x = ↑(f.support.equivFin ⟨x, hx⟩) :=
      Function.Injective.extend_apply Subtype.val_injective _ _ ⟨x, hx⟩
  let einv : ℕ → ι := Function.extend (↑) (f.support.equivFin.symm ·) (fun _ ↦ f.nonempty.some)
  have H (x : _) (hx : x ∈ f.support) : einv (e x) = x := by simp [he, hx, einv, Fin.val_injective]
  convert IsConvexMetricSpace.dist_convexCombination_map_le' (f.map e) (x ∘ einv) (y ∘ einv)
    using 3
  · ext1
    simp only [StdSimplex.map, ← Finsupp.mapDomain_comp]
    exact Finsupp.mapDomain_congr fun x hx ↦ by simp [H, hx]
  · ext1
    simp only [StdSimplex.map, ← Finsupp.mapDomain_comp]
    exact Finsupp.mapDomain_congr fun x hx ↦ by simp [H, hx]
  · simp only [StdSimplex.map, Function.comp_apply, zero_mul, implies_true, add_mul,
      Finsupp.sum_mapDomain_index]
    exact Finsupp.sum_congr fun x hx ↦ by simp [H, hx]

lemma dist_convexCombination_left_le (f : StdSimplex ℝ X) (x : X) :
    dist (convexCombination f) x ≤ f.weights.sum fun i r ↦ r * dist i x := by
  simpa using dist_convexCombination_map_le f id (fun _ ↦ x)

lemma dist_convexCombination_right_le (f : StdSimplex ℝ X) (x : X) :
    dist x (convexCombination f) ≤ f.weights.sum fun i r ↦ r * dist x i := by
  simpa using dist_convexCombination_map_le f (fun _ ↦ x) id
