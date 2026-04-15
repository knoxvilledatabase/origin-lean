/-
Extracted from Analysis/Normed/Group/AddTorsor.lean
Genuine: 7 of 12 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
# Torsors of additive normed group actions.

This file defines torsors of additive normed group actions, with a
metric space structure.  The motivating case is Euclidean affine
spaces.
-/

noncomputable section

open NNReal Topology

open Filter

class NormedAddTorsor (V : outParam Type*) (P : Type*) [SeminormedAddCommGroup V]
  [PseudoMetricSpace P] extends AddTorsor V P where
  dist_eq_norm' : ∀ x y : P, dist x y = ‖(x -ᵥ y : V)‖

-- INSTANCE (free from Core): (priority

variable {α V P W Q : Type*} [SeminormedAddCommGroup V] [PseudoMetricSpace P] [NormedAddTorsor V P]
  [NormedAddCommGroup W] [MetricSpace Q] [NormedAddTorsor W Q]

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): AffineSubspace.toNormedAddTorsor

-- INSTANCE (free from Core): :

variable (V W)

theorem dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖ :=
  NormedAddTorsor.dist_eq_norm' x y

theorem nndist_eq_nnnorm_vsub (x y : P) : nndist x y = ‖x -ᵥ y‖₊ :=
  NNReal.eq <| dist_eq_norm_vsub V x y

theorem dist_eq_norm_vsub' (x y : P) : dist x y = ‖y -ᵥ x‖ :=
  (dist_comm _ _).trans (dist_eq_norm_vsub _ _ _)

theorem nndist_eq_nnnorm_vsub' (x y : P) : nndist x y = ‖y -ᵥ x‖₊ :=
  NNReal.eq <| dist_eq_norm_vsub' V x y

end

theorem dist_vadd_cancel_left (v : V) (x y : P) : dist (v +ᵥ x) (v +ᵥ y) = dist x y :=
  dist_vadd _ _ _

theorem nndist_vadd_cancel_left (v : V) (x y : P) : nndist (v +ᵥ x) (v +ᵥ y) = nndist x y :=
  NNReal.eq <| dist_vadd_cancel_left _ _ _
