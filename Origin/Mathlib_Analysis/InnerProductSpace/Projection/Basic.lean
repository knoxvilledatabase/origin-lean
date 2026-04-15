/-
Extracted from Analysis/InnerProductSpace/Projection/Basic.lean
Genuine: 7 of 13 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core

/-!
# The orthogonal projection

Given a nonempty subspace `K` of an inner product space `E` such that `K`
admits an orthogonal projection, this file constructs
`K.orthogonalProjection : E →L[𝕜] K`, the orthogonal projection of `E` onto `K`. This map
satisfies: for any point `u` in `E`, the point `v = K.orthogonalProjection u` in `K` minimizes the
distance `‖u - v‖` to `u`.

This file also defines `K.starProjection : E →L[𝕜] E` which is the
orthogonal projection of `E` onto `K` but as a map from `E` to `E` instead of `E` to `K`.

Basic API for `orthogonalProjection` and `starProjection` is developed.

## References

The orthogonal projection construction is adapted from
* [Clément & Martin, *The Lax-Milgram Theorem. A detailed proof to be formalized in Coq*]
* [Clément & Martin, *A Coq formal proof of the Lax–Milgram theorem*]

The Coq code is available at the following address: <http://www.lri.fr/~sboldo/elfic/index.html>
-/

variable {𝕜 E F : Type*} [RCLike 𝕜]

variable [NormedAddCommGroup E] [NormedAddCommGroup F]

variable [InnerProductSpace 𝕜 E] [InnerProductSpace ℝ F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

local notation "absR" => @abs ℝ _ _

namespace Submodule

class HasOrthogonalProjection (K : Submodule 𝕜 E) : Prop where
  exists_orthogonal (v : E) : ∃ w ∈ K, v - w ∈ Kᗮ

variable (K : Submodule 𝕜 E)

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): [K.HasOrthogonalProjection]

-- INSTANCE (free from Core): HasOrthogonalProjection.map_linearIsometryEquiv

-- INSTANCE (free from Core): HasOrthogonalProjection.map_linearIsometryEquiv'

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): (K

noncomputable section

section orthogonalProjection

variable [K.HasOrthogonalProjection]

def orthogonalProjectionFn (v : E) :=
  (HasOrthogonalProjection.exists_orthogonal (K := K) v).choose

variable {K}

theorem orthogonalProjectionFn_mem (v : E) : K.orthogonalProjectionFn v ∈ K :=
  (HasOrthogonalProjection.exists_orthogonal (K := K) v).choose_spec.left

theorem orthogonalProjectionFn_inner_eq_zero (v : E) :
    ∀ w ∈ K, ⟪v - K.orthogonalProjectionFn v, w⟫ = 0 :=
  (K.mem_orthogonal' _).1 (HasOrthogonalProjection.exists_orthogonal (K := K) v).choose_spec.right

theorem eq_orthogonalProjectionFn_of_mem_of_inner_eq_zero {u v : E} (hvm : v ∈ K)
    (hvo : ∀ w ∈ K, ⟪u - v, w⟫ = 0) : K.orthogonalProjectionFn u = v := by
  rw [← sub_eq_zero, ← @inner_self_eq_zero 𝕜]
  have hvs : K.orthogonalProjectionFn u - v ∈ K :=
    Submodule.sub_mem K (orthogonalProjectionFn_mem u) hvm
  have huo : ⟪u - K.orthogonalProjectionFn u, K.orthogonalProjectionFn u - v⟫ = 0 :=
    orthogonalProjectionFn_inner_eq_zero u _ hvs
  have huv : ⟪u - v, K.orthogonalProjectionFn u - v⟫ = 0 := hvo _ hvs
  have houv : ⟪u - v - (u - K.orthogonalProjectionFn u), K.orthogonalProjectionFn u - v⟫ = 0 := by
    rw [inner_sub_left, huo, huv, sub_zero]
  rwa [sub_sub_sub_cancel_left] at houv

variable (K)

theorem orthogonalProjectionFn_norm_sq (v : E) :
    ‖v‖ * ‖v‖ =
      ‖v - K.orthogonalProjectionFn v‖ * ‖v - K.orthogonalProjectionFn v‖ +
        ‖K.orthogonalProjectionFn v‖ * ‖K.orthogonalProjectionFn v‖ := by
  set p := K.orthogonalProjectionFn v
  have h' : ⟪v - p, p⟫ = 0 :=
    orthogonalProjectionFn_inner_eq_zero _ _ (orthogonalProjectionFn_mem v)
  convert norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (v - p) p h' using 2 <;> simp

def orthogonalProjection : E →L[𝕜] K :=
  LinearMap.mkContinuous
    { toFun := fun v => ⟨K.orthogonalProjectionFn v, orthogonalProjectionFn_mem v⟩
      map_add' := fun x y => by
        have hm : K.orthogonalProjectionFn x + K.orthogonalProjectionFn y ∈ K :=
          Submodule.add_mem K (orthogonalProjectionFn_mem x) (orthogonalProjectionFn_mem y)
        have ho :
          ∀ w ∈ K, ⟪x + y - (K.orthogonalProjectionFn x + K.orthogonalProjectionFn y), w⟫ = 0 := by
          intro w hw
          rw [add_sub_add_comm, inner_add_left, orthogonalProjectionFn_inner_eq_zero _ w hw,
            orthogonalProjectionFn_inner_eq_zero _ w hw, add_zero]
        ext
        simp [eq_orthogonalProjectionFn_of_mem_of_inner_eq_zero hm ho]
      map_smul' := fun c x => by
        have hm : c • K.orthogonalProjectionFn x ∈ K :=
          Submodule.smul_mem K _ (orthogonalProjectionFn_mem x)
        have ho : ∀ w ∈ K, ⟪c • x - c • K.orthogonalProjectionFn x, w⟫ = 0 := by
          intro w hw
          rw [← smul_sub, inner_smul_left, orthogonalProjectionFn_inner_eq_zero _ w hw,
            mul_zero]
        ext
        simp [eq_orthogonalProjectionFn_of_mem_of_inner_eq_zero hm ho] }
    1 fun x => by
    simp only [one_mul, LinearMap.coe_mk]
    refine le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) ?_
    change ‖K.orthogonalProjectionFn x‖ ^ 2 ≤ ‖x‖ ^ 2
    nlinarith [K.orthogonalProjectionFn_norm_sq x]

variable {K}
