/-
Extracted from LinearAlgebra/Dimension/Free.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Rank of free modules

## Main result
- `LinearEquiv.nonempty_equiv_iff_lift_rank_eq`:
  Two free modules are isomorphic iff they have the same dimension.
- `Module.finBasis`:
  An arbitrary basis of a finite free module indexed by `Fin n` given `finrank R M = n`.

-/

noncomputable section

universe u v v' w

open Cardinal Basis Submodule Function Set Module

section Tower

variable (F : Type u) (K : Type v) (A : Type w)

variable [Semiring F] [Semiring K] [AddCommMonoid A]

variable [Module F K] [Module K A] [Module F A] [IsScalarTower F K A]

variable [StrongRankCondition F] [StrongRankCondition K] [Module.Free F K] [Module.Free K A]

theorem lift_rank_mul_lift_rank :
    Cardinal.lift.{w} (Module.rank F K) * Cardinal.lift.{v} (Module.rank K A) =
      Cardinal.lift.{v} (Module.rank F A) := by
  let b := Module.Free.chooseBasis F K
  let c := Module.Free.chooseBasis K A
  rw [← (Module.rank F K).lift_id, ← b.mk_eq_rank, ← (Module.rank K A).lift_id, ← c.mk_eq_rank,
    ← lift_umax.{w, v}, ← (b.smulTower c).mk_eq_rank, mk_prod, lift_mul, lift_lift, lift_lift,
    lift_lift, lift_lift, lift_umax.{v, w}]
