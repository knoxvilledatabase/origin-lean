/-
Extracted from Analysis/Normed/Module/MStructure.lean
Genuine: 7 of 8 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# M-structure

A projection P on a normed space X is said to be an L-projection (`IsLprojection`) if, for all `x`
in `X`,
$\|x\| = \|P x\| + \|(1 - P) x\|$.

A projection P on a normed space X is said to be an M-projection if, for all `x` in `X`,
$\|x\| = max(\|P x\|,\|(1 - P) x\|)$.

The L-projections on `X` form a Boolean algebra (`IsLprojection.Subtype.BooleanAlgebra`).

## TODO (Motivational background)

The M-projections on a normed space form a Boolean algebra.

The range of an L-projection on a normed space `X` is said to be an L-summand of `X`. The range of
an M-projection is said to be an M-summand of `X`.

When `X` is a Banach space, the Boolean algebra of L-projections is complete. Let `X` be a normed
space with dual `X^*`. A closed subspace `M` of `X` is said to be an M-ideal if the topological
annihilator `M^∘` is an L-summand of `X^*`.

M-ideal, M-summands and L-summands were introduced by Alfsen and Effros in [alfseneffros1972] to
study the structure of general Banach spaces. When `A` is a JB*-triple, the M-ideals of `A` are
exactly the norm-closed ideals of `A`. When `A` is a JBW*-triple with predual `X`, the M-summands of
`A` are exactly the weak*-closed ideals, and their pre-duals can be identified with the L-summands
of `X`. In the special case when `A` is a C*-algebra, the M-ideals are exactly the norm-closed
two-sided ideals of `A`, when `A` is also a W*-algebra the M-summands are exactly the weak*-closed
two-sided ideals of `A`.

## Implementation notes

The approach to showing that the L-projections form a Boolean algebra is inspired by
`MeasureTheory.MeasurableSpace`.

Instead of using `P : X →L[𝕜] X` to represent projections, we use an arbitrary ring `M` with a
faithful action on `X`. `ContinuousLinearMap.apply_module` can be used to recover the `X →L[𝕜] X`
special case.

## References

* [Behrends, M-structure and the Banach-Stone Theorem][behrends1979]
* [Harmand, Werner, Werner, M-ideals in Banach spaces and Banach algebras][harmandwernerwerner1993]

## Tags

M-summand, M-projection, L-summand, L-projection, M-ideal, M-structure

-/

variable (X : Type*) [NormedAddCommGroup X]

variable {M : Type*} [Ring M] [Module M X]

structure IsLprojection (P : M) : Prop where
  proj : IsIdempotentElem P
  Lnorm : ∀ x : X, ‖x‖ = ‖P • x‖ + ‖(1 - P) • x‖

structure IsMprojection (P : M) : Prop where
  proj : IsIdempotentElem P
  Mnorm : ∀ x : X, ‖x‖ = max ‖P • x‖ ‖(1 - P) • x‖

variable {X}

namespace IsLprojection

theorem Lcomplement {P : M} (h : IsLprojection X P) : IsLprojection X (1 - P) :=
  ⟨h.proj.one_sub, fun x => by
    rw [add_comm, sub_sub_cancel]
    exact h.Lnorm x⟩

theorem Lcomplement_iff (P : M) : IsLprojection X P ↔ IsLprojection X (1 - P) :=
  ⟨Lcomplement, fun h => sub_sub_cancel 1 P ▸ h.Lcomplement⟩

theorem commute [FaithfulSMul M X] {P Q : M} (h₁ : IsLprojection X P) (h₂ : IsLprojection X Q) :
    Commute P Q := by
  have PR_eq_RPR : ∀ R : M, IsLprojection X R → P * R = R * P * R := fun R h₃ => by
    refine @eq_of_smul_eq_smul _ X _ _ _ _ fun x => by
      rw [← norm_sub_eq_zero_iff]
      have e1 : ‖R • x‖ ≥ ‖R • x‖ + 2 • ‖(P * R) • x - (R * P * R) • x‖ :=
        calc
          ‖R • x‖ = ‖R • P • R • x‖ + ‖(1 - R) • P • R • x‖ +
              (‖(R * R) • x - R • P • R • x‖ + ‖(1 - R) • (1 - P) • R • x‖) := by
            rw [h₁.Lnorm, h₃.Lnorm, h₃.Lnorm ((1 - P) • R • x), sub_smul 1 P, one_smul, smul_sub,
              mul_smul]
          _ = ‖R • P • R • x‖ + ‖(1 - R) • P • R • x‖ +
              (‖R • x - R • P • R • x‖ + ‖((1 - R) * R) • x - (1 - R) • P • R • x‖) := by
            rw [h₃.proj.eq, sub_smul 1 P, one_smul, smul_sub, mul_smul]
          _ = ‖R • P • R • x‖ + ‖(1 - R) • P • R • x‖ +
              (‖R • x - R • P • R • x‖ + ‖(1 - R) • P • R • x‖) := by
            rw [sub_mul, h₃.proj.eq, one_mul, sub_self, zero_smul, zero_sub, norm_neg]
          _ = ‖R • P • R • x‖ + ‖R • x - R • P • R • x‖ + 2 • ‖(1 - R) • P • R • x‖ := by abel
          _ ≥ ‖R • x‖ + 2 • ‖(P * R) • x - (R * P * R) • x‖ := by
            rw [ge_iff_le]
            have :=
              add_le_add_left (norm_le_insert' (R • x) (R • P • R • x)) (2 • ‖(1 - R) • P • R • x‖)
            simpa only [mul_smul, sub_smul, one_smul] using this
      rw [ge_iff_le] at e1
      nth_rewrite 2 [← add_zero ‖R • x‖] at e1
      rw [add_le_add_iff_left, two_smul, ← two_mul] at e1
      rw [le_antisymm_iff]
      refine ⟨?_, norm_nonneg _⟩
      rwa [← mul_zero (2 : ℝ), mul_le_mul_iff_right₀ (show (0 : ℝ) < 2 by simp)] at e1
  have QP_eq_QPQ : Q * P = Q * P * Q := by
    have e1 : P * (1 - Q) = P * (1 - Q) - (Q * P - Q * P * Q) :=
      calc
        P * (1 - Q) = (1 - Q) * P * (1 - Q) := by rw [PR_eq_RPR (1 - Q) h₂.Lcomplement]
        _ = P * (1 - Q) - (Q * P - Q * P * Q) := by noncomm_ring
    rwa [eq_sub_iff_add_eq, add_eq_left, sub_eq_zero] at e1
  change P * Q = Q * P
  rw [QP_eq_QPQ, PR_eq_RPR Q h₂]

theorem mul [FaithfulSMul M X] {P Q : M} (h₁ : IsLprojection X P) (h₂ : IsLprojection X Q) :
    IsLprojection X (P * Q) := by
  refine ⟨IsIdempotentElem.mul_of_commute (h₁.commute h₂) h₁.proj h₂.proj, ?_⟩
  intro x
  refine le_antisymm ?_ ?_
  · calc
      ‖x‖ = ‖(P * Q) • x + (x - (P * Q) • x)‖ := by rw [add_sub_cancel ((P * Q) • x) x]
      _ ≤ ‖(P * Q) • x‖ + ‖x - (P * Q) • x‖ := by apply norm_add_le
      _ = ‖(P * Q) • x‖ + ‖(1 - P * Q) • x‖ := by rw [sub_smul, one_smul]
  · calc
      ‖x‖ = ‖P • Q • x‖ + (‖Q • x - P • Q • x‖ + ‖x - Q • x‖) := by
        rw [h₂.Lnorm x, h₁.Lnorm (Q • x), sub_smul, one_smul, sub_smul, one_smul, add_assoc]
      _ ≥ ‖P • Q • x‖ + ‖Q • x - P • Q • x + (x - Q • x)‖ :=
        ((add_le_add_iff_left ‖P • Q • x‖).mpr (norm_add_le (Q • x - P • Q • x) (x - Q • x)))
      _ = ‖(P * Q) • x‖ + ‖(1 - P * Q) • x‖ := by
        rw [sub_add_sub_cancel', sub_smul, one_smul, mul_smul]

theorem join [FaithfulSMul M X] {P Q : M} (h₁ : IsLprojection X P) (h₂ : IsLprojection X Q) :
    IsLprojection X (P + Q - P * Q) := by
  convert (Lcomplement_iff _).mp (h₁.Lcomplement.mul h₂.Lcomplement) using 1
  noncomm_ring

-- INSTANCE (free from Core): Subtype.instCompl
