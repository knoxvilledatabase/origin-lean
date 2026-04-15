/-
Extracted from Geometry/Euclidean/SignedDist.lean
Genuine: 6 of 10 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Signed distance to an affine subspace in a Euclidean space.

This file defines the signed distance between two points, in the direction of a given vector, and
the signed distance between an affine subspace and a point, in the direction of a given
reference point.

## Main definitions

* `signedDist` is the signed distance between two points
* `AffineSubspace.signedInfDist` is the signed distance between an affine subspace and a point.
* `Affine.Simplex.signedInfDist` is the signed distance between a face of a simplex and a point.
  In the case of a triangle, these distances are trilinear coordinates.

## References

* https://en.wikipedia.org/wiki/Trilinear_coordinates

-/

open EuclideanGeometry NormedSpace

open scoped RealInnerProductSpace

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]

variable [NormedAddTorsor V P]

section signedDist

noncomputable def signedDist (v : V) : P →ᵃ[ℝ] P →ᴬ[ℝ] ℝ where
  toFun p := (innerSL ℝ (normalize v)).toContinuousAffineMap.comp
    (ContinuousAffineMap.id ℝ P -ᵥ .const ℝ P p)
  linear := {
    toFun w := .const ℝ P ⟪-normalize v, w⟫
    map_add' x y := by ext; simp [inner_add_right]
    map_smul' r x := by ext; simp [inner_smul_right] }
  map_vadd' p v' := by
    ext q
    simp [vsub_vadd_eq_vsub_sub, inner_sub_right, ← sub_eq_neg_add]

variable (v w : V) (p q r : P)

lemma signedDist_apply_linear : (signedDist v p).linear = innerₗ V (normalize v) := by
  change (innerₗ V (normalize v)).comp (LinearMap.id - 0) = _
  simp

lemma signedDist_apply_linear_apply : (signedDist v p).linear w = ⟪normalize v, w⟫ := by
  simp [signedDist_apply_linear]

lemma signedDist_smul (r : ℝ) : signedDist (r • v) p q = SignType.sign r * signedDist v p q := by
  simp only [signedDist_apply_apply]
  rw [normalize_smul, real_inner_smul_left]

lemma signedDist_smul_of_pos {r : ℝ} (h : 0 < r) : signedDist (r • v) p q = signedDist v p q := by
  simp [signedDist_smul, h]

lemma signedDist_smul_of_neg {r : ℝ} (h : r < 0) : signedDist (r • v) p q = -signedDist v p q := by
  simp [signedDist_smul, h]
