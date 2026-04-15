/-
Extracted from Topology/MetricSpace/Gluing.lean
Genuine: 12 of 12 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Metric space gluing

Gluing two metric spaces along a common subset. Formally, we are given

```
     Φ
  Z ---> X
  |
  |Ψ
  v
  Y
```
where `hΦ : Isometry Φ` and `hΨ : Isometry Ψ`.
We want to complete the square by a space `GlueSpace hΦ hΨ` and two isometries
`toGlueL hΦ hΨ` and `toGlueR hΦ hΨ` that make the square commute.
We start by defining a predistance on the disjoint union `X ⊕ Y`, for which
points `Φ p` and `Ψ p` are at distance 0. The (quotient) metric space associated
to this predistance is the desired space.

This is an instance of a more general construction, where `Φ` and `Ψ` do not have to be isometries,
but the distances in the image almost coincide, up to `2ε` say. Then one can almost glue the two
spaces so that the images of a point under `Φ` and `Ψ` are `ε`-close. If `ε > 0`, this yields a
metric space structure on `X ⊕ Y`, without the need to take a quotient. In particular,
this gives a natural metric space structure on `X ⊕ Y`, where the basepoints
are at distance 1, say, and the distances between other points are obtained by going through the two
basepoints.
(We also register the same metric space structure on a general disjoint union `Σ i, E i`).

We also define the inductive limit of metric spaces. Given
```
     f 0        f 1        f 2        f 3
X 0 -----> X 1 -----> X 2 -----> X 3 -----> ...
```
where the `X n` are metric spaces and `f n` isometric embeddings, we define the inductive
limit of the `X n`, also known as the increasing union of the `X n` in this context, if we
identify `X n` and `X (n+1)` through `f n`. This is a metric space in which all `X n` embed
isometrically and in a way compatible with `f n`.

-/

noncomputable section

universe u v w

open Function Set Uniformity Topology

namespace Metric

section ApproxGluing

variable {X : Type u} {Y : Type v} {Z : Type w}

variable [MetricSpace X] [MetricSpace Y] {Φ : Z → X} {Ψ : Z → Y} {ε : ℝ}

def glueDist (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ) : X ⊕ Y → X ⊕ Y → ℝ
  | .inl x, .inl y => dist x y
  | .inr x, .inr y => dist x y
  | .inl x, .inr y => (⨅ p, dist x (Φ p) + dist y (Ψ p)) + ε
  | .inr x, .inl y => (⨅ p, dist y (Φ p) + dist x (Ψ p)) + ε

set_option backward.privateInPublic true in

private theorem glueDist_self (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ) : ∀ x, glueDist Φ Ψ ε x x = 0
  | .inl _ => dist_self _
  | .inr _ => dist_self _

theorem glueDist_glued_points [Nonempty Z] (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ) (p : Z) :
    glueDist Φ Ψ ε (.inl (Φ p)) (.inr (Ψ p)) = ε := by
  have : ⨅ q, dist (Φ p) (Φ q) + dist (Ψ p) (Ψ q) = 0 := by
    have A : ∀ q, 0 ≤ dist (Φ p) (Φ q) + dist (Ψ p) (Ψ q) := fun _ => by positivity
    refine le_antisymm ?_ (le_ciInf A)
    have : 0 = dist (Φ p) (Φ p) + dist (Ψ p) (Ψ p) := by simp
    rw [this]
    exact ciInf_le ⟨0, forall_mem_range.2 A⟩ p
  simp only [glueDist, this, zero_add]

set_option backward.privateInPublic true in

private theorem glueDist_comm (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ) :
    ∀ x y, glueDist Φ Ψ ε x y = glueDist Φ Ψ ε y x
  | .inl _, .inl _ => dist_comm _ _
  | .inr _, .inr _ => dist_comm _ _
  | .inl _, .inr _ => rfl
  | .inr _, .inl _ => rfl

theorem glueDist_swap (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ) :
    ∀ x y, glueDist Ψ Φ ε x.swap y.swap = glueDist Φ Ψ ε x y
  | .inl _, .inl _ => rfl
  | .inr _, .inr _ => rfl
  | .inl _, .inr _ => by simp only [glueDist, Sum.swap_inl, Sum.swap_inr, add_comm]
  | .inr _, .inl _ => by simp only [glueDist, Sum.swap_inl, Sum.swap_inr, add_comm]

theorem le_glueDist_inl_inr (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ) (x y) :
    ε ≤ glueDist Φ Ψ ε (.inl x) (.inr y) :=
  le_add_of_nonneg_left <| Real.iInf_nonneg fun _ => by positivity

theorem le_glueDist_inr_inl (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ) (x y) :
    ε ≤ glueDist Φ Ψ ε (.inr x) (.inl y) := by
  rw [glueDist_comm]; apply le_glueDist_inl_inr

variable [Nonempty Z]

private theorem glueDist_triangle_inl_inr_inr (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ) (x : X) (y z : Y) :
    glueDist Φ Ψ ε (.inl x) (.inr z) ≤
      glueDist Φ Ψ ε (.inl x) (.inr y) + glueDist Φ Ψ ε (.inr y) (.inr z) := by
  simp only [glueDist]
  rw [add_right_comm, add_le_add_iff_right]
  refine le_ciInf_add fun p => ciInf_le_of_le ⟨0, ?_⟩ p ?_
  · exact forall_mem_range.2 fun _ => by positivity
  · linarith [dist_triangle_left z (Ψ p) y]

private theorem glueDist_triangle_inl_inr_inl (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ)
    (H : ∀ p q, |dist (Φ p) (Φ q) - dist (Ψ p) (Ψ q)| ≤ 2 * ε) (x : X) (y : Y) (z : X) :
    glueDist Φ Ψ ε (.inl x) (.inl z) ≤
      glueDist Φ Ψ ε (.inl x) (.inr y) + glueDist Φ Ψ ε (.inr y) (.inl z) := by
  simp_rw [glueDist, add_add_add_comm _ ε, add_assoc]
  refine le_ciInf_add fun p => ?_
  rw [add_left_comm, add_assoc, ← two_mul]
  refine le_ciInf_add fun q => ?_
  rw [dist_comm z]
  linarith [dist_triangle4 x (Φ p) (Φ q) z, dist_triangle_left (Ψ p) (Ψ q) y, (abs_le.1 (H p q)).2]

set_option backward.privateInPublic true in

private theorem glueDist_triangle (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ)
    (H : ∀ p q, |dist (Φ p) (Φ q) - dist (Ψ p) (Ψ q)| ≤ 2 * ε) :
    ∀ x y z, glueDist Φ Ψ ε x z ≤ glueDist Φ Ψ ε x y + glueDist Φ Ψ ε y z
  | .inl _, .inl _, .inl _ => dist_triangle _ _ _
  | .inr _, .inr _, .inr _ => dist_triangle _ _ _
  | .inr x, .inl y, .inl z => by
    simp only [← glueDist_swap Φ]
    apply glueDist_triangle_inl_inr_inr
  | .inr x, .inr y, .inl z => by
    simpa only [glueDist_comm, add_comm] using glueDist_triangle_inl_inr_inr _ _ _ z y x
  | .inl x, .inl y, .inr z => by
    simpa only [← glueDist_swap Φ, glueDist_comm, add_comm, Sum.swap_inl, Sum.swap_inr]
      using glueDist_triangle_inl_inr_inr Ψ Φ ε z y x
  | .inl _, .inr _, .inr _ => glueDist_triangle_inl_inr_inr ..
  | .inl x, .inr y, .inl z => glueDist_triangle_inl_inr_inl Φ Ψ ε H x y z
  | .inr x, .inl y, .inr z => by
    simp only [← glueDist_swap Φ]
    apply glueDist_triangle_inl_inr_inl
    simpa only [abs_sub_comm]

end

set_option backward.privateInPublic true in

private theorem eq_of_glueDist_eq_zero (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ) (ε0 : 0 < ε) :
    ∀ p q : X ⊕ Y, glueDist Φ Ψ ε p q = 0 → p = q
  | .inl x, .inl y, h => by rw [eq_of_dist_eq_zero h]
  | .inl x, .inr y, h => by exfalso; linarith [le_glueDist_inl_inr Φ Ψ ε x y]
  | .inr x, .inl y, h => by exfalso; linarith [le_glueDist_inr_inl Φ Ψ ε x y]
  | .inr x, .inr y, h => by rw [eq_of_dist_eq_zero h]

theorem Sum.mem_uniformity_iff_glueDist (hε : 0 < ε) (s : Set ((X ⊕ Y) × (X ⊕ Y))) :
    s ∈ 𝓤 (X ⊕ Y) ↔ ∃ δ > 0, ∀ a b, glueDist Φ Ψ ε a b < δ → (a, b) ∈ s := by
  simp only [Sum.uniformity, Filter.mem_sup, Filter.mem_map, mem_uniformity_dist, mem_preimage]
  constructor
  · rintro ⟨⟨δX, δX0, hX⟩, δY, δY0, hY⟩
    refine ⟨min (min δX δY) ε, lt_min (lt_min δX0 δY0) hε, ?_⟩
    rintro (a | a) (b | b) h <;> simp only [lt_min_iff] at h
    · exact hX h.1.1
    · exact absurd h.2 (le_glueDist_inl_inr _ _ _ _ _).not_gt
    · exact absurd h.2 (le_glueDist_inr_inl _ _ _ _ _).not_gt
    · exact hY h.1.2
  · rintro ⟨ε, ε0, H⟩
    constructor <;> exact ⟨ε, ε0, fun _ _ h => H _ _ h⟩

set_option backward.privateInPublic true in

set_option backward.privateInPublic.warn false in
