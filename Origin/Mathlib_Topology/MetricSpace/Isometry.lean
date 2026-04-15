/-
Extracted from Topology/MetricSpace/Isometry.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Isometries

We define isometries, i.e., maps between emetric spaces that preserve
the edistance (on metric spaces, these are exactly the maps that preserve distances),
and prove their basic properties. We also introduce isometric bijections.

Since a lot of elementary properties don't require `eq_of_dist_eq_zero` we start setting up the
theory for `PseudoMetricSpace` and we specialize to `MetricSpace` when needed.
-/

open Topology

noncomputable section

universe u v w

variable {F ι : Type*} {α : Type u} {β : Type v} {γ : Type w}

open Function Set

open scoped Topology ENNReal

def Isometry [PseudoEMetricSpace α] [PseudoEMetricSpace β] (f : α → β) : Prop :=
  ∀ x1 x2 : α, edist (f x1) (f x2) = edist x1 x2

theorem isometry_iff_nndist_eq [PseudoMetricSpace α] [PseudoMetricSpace β] {f : α → β} :
    Isometry f ↔ ∀ x y, nndist (f x) (f y) = nndist x y := by
  simp only [Isometry, edist_nndist, ENNReal.coe_inj]

theorem isometry_iff_dist_eq [PseudoMetricSpace α] [PseudoMetricSpace β] {f : α → β} :
    Isometry f ↔ ∀ x y, dist (f x) (f y) = dist x y := by
  simp only [isometry_iff_nndist_eq, ← coe_nndist, NNReal.coe_inj]

alias ⟨Isometry.dist_eq, _⟩ := isometry_iff_dist_eq

alias ⟨_, Isometry.of_dist_eq⟩ := isometry_iff_dist_eq

alias ⟨Isometry.nndist_eq, _⟩ := isometry_iff_nndist_eq

alias ⟨_, Isometry.of_nndist_eq⟩ := isometry_iff_nndist_eq

namespace Isometry

section PseudoEMetricIsometry

variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] [PseudoEMetricSpace γ]

variable {f : α → β} {x : α}

theorem edist_eq (hf : Isometry f) (x y : α) : edist (f x) (f y) = edist x y :=
  hf x y

theorem lipschitz (h : Isometry f) : LipschitzWith 1 f :=
  LipschitzWith.of_edist_le fun x y => (h x y).le

theorem antilipschitz (h : Isometry f) : AntilipschitzWith 1 f := fun x y => by
  simp only [h x y, ENNReal.coe_one, one_mul, le_refl]
