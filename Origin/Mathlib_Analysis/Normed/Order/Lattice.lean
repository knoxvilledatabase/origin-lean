/-
Extracted from Analysis/Normed/Order/Lattice.lean
Genuine: 15 of 22 | Dissolved: 0 | Infrastructure: 7
-/
import Origin.Core

/-!
# Normed lattice ordered groups

Motivated by the theory of Banach Lattices, we then define `NormedLatticeAddCommGroup` as a
lattice with a covariant normed group addition satisfying the solid axiom.

## Main statements

We show that a normed lattice ordered group is a topological lattice with respect to the norm
topology.

## References

* [Meyer-Nieberg, Banach lattices][MeyerNieberg1991]

## Tags

normed, lattice, ordered, group
-/

/-!
### Normed lattice ordered groups

Motivated by the theory of Banach Lattices, this section introduces normed lattice ordered groups.
-/

section SolidNorm

class HasSolidNorm (α : Type*) [NormedAddCommGroup α] [Lattice α] : Prop where
  solid : ∀ ⦃x y : α⦄, |x| ≤ |y| → ‖x‖ ≤ ‖y‖

variable {α : Type*} [NormedAddCommGroup α] [Lattice α] [HasSolidNorm α]

theorem norm_le_norm_of_abs_le_abs {a b : α} (h : |a| ≤ |b|) : ‖a‖ ≤ ‖b‖ :=
  HasSolidNorm.solid h

theorem LatticeOrderedAddCommGroup.isSolid_ball (r : ℝ) :
    LatticeOrderedAddCommGroup.IsSolid (Metric.ball (0 : α) r) := fun _ hx _ hxy =>
  mem_ball_zero_iff.mpr ((HasSolidNorm.solid hxy).trans_lt (mem_ball_zero_iff.mp hx))

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): Int.hasSolidNorm

end SolidNorm

variable {α : Type*} [NormedAddCommGroup α] [Lattice α] [HasSolidNorm α] [IsOrderedAddMonoid α]

open HasSolidNorm

theorem dual_solid (a b : α) (h : b ⊓ -b ≤ a ⊓ -a) : ‖a‖ ≤ ‖b‖ := by
  apply solid
  rw [abs]
  nth_rw 1 [← neg_neg a]
  rw [← neg_inf]
  rw [abs]
  nth_rw 1 [← neg_neg b]
  rwa [← neg_inf, neg_le_neg_iff, inf_comm _ b, inf_comm _ a]

-- INSTANCE (free from Core): (priority

theorem norm_abs_eq_norm (a : α) : ‖|a|‖ = ‖a‖ :=
  (solid (abs_abs a).le).antisymm (solid (abs_abs a).symm.le)

theorem norm_inf_sub_inf_le_add_norm (a b c d : α) : ‖a ⊓ b - c ⊓ d‖ ≤ ‖a - c‖ + ‖b - d‖ := by
  rw [← norm_abs_eq_norm (a - c), ← norm_abs_eq_norm (b - d)]
  refine le_trans (solid ?_) (norm_add_le |a - c| |b - d|)
  rw [abs_of_nonneg (add_nonneg (abs_nonneg (a - c)) (abs_nonneg (b - d)))]
  calc
    |a ⊓ b - c ⊓ d| = |a ⊓ b - c ⊓ b + (c ⊓ b - c ⊓ d)| := by rw [sub_add_sub_cancel]
    _ ≤ |a ⊓ b - c ⊓ b| + |c ⊓ b - c ⊓ d| := abs_add_le _ _
    _ ≤ |a - c| + |b - d| := by
      gcongr ?_ + ?_
      · exact abs_inf_sub_inf_le_abs _ _ _
      · rw [inf_comm c, inf_comm c]
        exact abs_inf_sub_inf_le_abs _ _ _

theorem norm_sup_sub_sup_le_add_norm (a b c d : α) : ‖a ⊔ b - c ⊔ d‖ ≤ ‖a - c‖ + ‖b - d‖ := by
  rw [← norm_abs_eq_norm (a - c), ← norm_abs_eq_norm (b - d)]
  refine le_trans (solid ?_) (norm_add_le |a - c| |b - d|)
  rw [abs_of_nonneg (add_nonneg (abs_nonneg (a - c)) (abs_nonneg (b - d)))]
  calc
    |a ⊔ b - c ⊔ d| = |a ⊔ b - c ⊔ b + (c ⊔ b - c ⊔ d)| := by rw [sub_add_sub_cancel]
    _ ≤ |a ⊔ b - c ⊔ b| + |c ⊔ b - c ⊔ d| := abs_add_le _ _
    _ ≤ |a - c| + |b - d| := by
      gcongr ?_ + ?_
      · exact abs_sup_sub_sup_le_abs _ _ _
      · rw [sup_comm c, sup_comm c]
        exact abs_sup_sub_sup_le_abs _ _ _

theorem norm_inf_le_add (x y : α) : ‖x ⊓ y‖ ≤ ‖x‖ + ‖y‖ := by
  have h : ‖x ⊓ y - 0 ⊓ 0‖ ≤ ‖x - 0‖ + ‖y - 0‖ := norm_inf_sub_inf_le_add_norm x y 0 0
  simpa only [inf_idem, sub_zero] using h

theorem norm_sup_le_add (x y : α) : ‖x ⊔ y‖ ≤ ‖x‖ + ‖y‖ := by
  have h : ‖x ⊔ y - 0 ⊔ 0‖ ≤ ‖x - 0‖ + ‖y - 0‖ := norm_sup_sub_sup_le_add_norm x y 0 0
  simpa only [sup_idem, sub_zero] using h

-- INSTANCE (free from Core): (priority

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

theorem norm_abs_sub_abs (a b : α) : ‖|a| - |b|‖ ≤ ‖a - b‖ := solid (abs_abs_sub_abs_le _ _)

theorem norm_sup_sub_sup_le_norm (x y z : α) : ‖x ⊔ z - y ⊔ z‖ ≤ ‖x - y‖ :=
  solid (abs_sup_sub_sup_le_abs x y z)

theorem norm_inf_sub_inf_le_norm (x y z : α) : ‖x ⊓ z - y ⊓ z‖ ≤ ‖x - y‖ :=
  solid (abs_inf_sub_inf_le_abs x y z)

theorem lipschitzWith_sup_right (z : α) : LipschitzWith 1 fun x => x ⊔ z :=
  LipschitzWith.of_dist_le_mul fun x y => by
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
    exact norm_sup_sub_sup_le_norm x y z

lemma lipschitzWith_posPart : LipschitzWith 1 (posPart : α → α) :=
  lipschitzWith_sup_right 0

lemma lipschitzWith_negPart : LipschitzWith 1 (negPart : α → α) := by
  simpa [Function.comp] using lipschitzWith_posPart.comp LipschitzWith.id.neg
