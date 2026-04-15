/-
Extracted from LinearAlgebra/FreeModule/Finite/Matrix.lean
Genuine: 6 of 9 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Finite and free modules using matrices

We provide some instances for finite and free modules involving matrices.

## Main results

* `Module.Free.linearMap` : if `M` and `N` are finite and free, then `M →ₗ[R] N` is free.
* `Module.Finite.ofBasis` : A free module with a basis indexed by a `Fintype` is finite.
* `Module.Finite.linearMap` : if `M` and `N` are finite and free, then `M →ₗ[R] N`
  is finite.
-/

universe u u' v w

variable (R : Type u) (S : Type u') (M : Type v) (N : Type w)

open Module.Free (chooseBasis ChooseBasisIndex)

open Module (finrank)

section Ring

variable [Ring R] [Ring S] [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]

variable [AddCommGroup N] [Module R N] [Module S N] [SMulCommClass R S N]

private noncomputable def linearMapEquivFun : (M →ₗ[R] N) ≃ₗ[S] ChooseBasisIndex R M → N :=
  (chooseBasis R M).repr.congrLeft N S ≪≫ₗ (Finsupp.lsum S).symm ≪≫ₗ
    LinearEquiv.piCongrRight fun _ ↦ LinearMap.ringLmapEquivSelf R S N

-- INSTANCE (free from Core): Module.Free.linearMap

-- INSTANCE (free from Core): Module.Finite.linearMap

variable [StrongRankCondition R] [StrongRankCondition S] [Module.Free S N]

open Cardinal

theorem Module.rank_linearMap :
    Module.rank S (M →ₗ[R] N) = lift.{w} (Module.rank R M) * lift.{v} (Module.rank S N) := by
  rw [(linearMapEquivFun R S M N).rank_eq, rank_fun_eq_lift_mul,
    ← finrank_eq_card_chooseBasisIndex, ← finrank_eq_rank R, lift_natCast]

theorem Module.finrank_linearMap :
    finrank S (M →ₗ[R] N) = finrank R M * finrank S N := by
  simp_rw [finrank, rank_linearMap, toNat_mul, toNat_lift]

variable [Module R S] [SMulCommClass R S S]

theorem Module.rank_linearMap_self :
    Module.rank S (M →ₗ[R] S) = lift.{u'} (Module.rank R M) := by
  rw [rank_linearMap, rank_self, lift_one, mul_one]

theorem Module.finrank_linearMap_self : finrank S (M →ₗ[R] S) = finrank R M := by
  rw [finrank_linearMap, finrank_self, mul_one]

end Ring

section AlgHom

variable (K M : Type*) (L : Type v) [CommRing K] [Ring M] [Algebra K M]
  [Module.Free K M] [Module.Finite K M] [CommRing L] [IsDomain L] [Algebra K L]

-- INSTANCE (free from Core): Finite.algHom

open Cardinal

theorem cardinalMk_algHom_le_rank : #(M →ₐ[K] L) ≤ lift.{v} (Module.rank K M) := by
  convert (linearIndependent_algHom_toLinearMap K M L).cardinal_lift_le_rank
  · rw [lift_id]
  · have := Module.nontrivial K L
    rw [lift_id, Module.rank_linearMap_self]
