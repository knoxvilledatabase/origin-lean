/-
Extracted from Algebra/Lie/Sl2.lean
Genuine: 7 | Conflates: 0 | Dissolved: 7 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!

# The Lie algebra `sl₂` and its representations

The Lie algebra `sl₂` is the unique simple Lie algebra of minimal rank, 1, and as such occupies a
distinguished position in the general theory. This file provides some basic definitions and results
about `sl₂`.

## Main definitions:
 * `IsSl2Triple`: a structure representing a triple of elements in a Lie algebra which satisfy the
   standard relations for `sl₂`.
 * `IsSl2Triple.HasPrimitiveVectorWith`: a structure representing a primitive vector in a
   representation of a Lie algebra relative to a distinguished `sl₂` triple.
 * `IsSl2Triple.HasPrimitiveVectorWith.exists_nat`: the eigenvalue of a primitive vector must be a
   natural number if the representation is finite-dimensional.

-/

variable (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

open LieModule Set

variable {L} in

-- DISSOLVED: IsSl2Triple

namespace IsSl2Triple

variable {L M}

variable {h e f : L}

-- DISSOLVED: symm

@[simp] lemma symm_iff : IsSl2Triple (-h) f e ↔ IsSl2Triple h e f :=
  ⟨fun t ↦ neg_neg h ▸ t.symm, symm⟩

lemma lie_h_e_smul (t : IsSl2Triple h e f) : ⁅h, e⁆ = (2 : R) • e := by
  simp [t.lie_h_e_nsmul, two_smul]

lemma lie_lie_smul_f (t : IsSl2Triple h e f) : ⁅h, f⁆ = -((2 : R) • f) := by
  simp [t.lie_h_f_nsmul, two_smul]

-- DISSOLVED: e_ne_zero

-- DISSOLVED: f_ne_zero

variable {R}

-- DISSOLVED: HasPrimitiveVectorWith

-- DISSOLVED: HasPrimitiveVectorWith.mk'

namespace HasPrimitiveVectorWith

variable {m : M} {μ : R} {t : IsSl2Triple h e f}

local notation "ψ" n => ((toEnd R L M f) ^ n) m

set_option linter.unusedVariables false in

@[nolint unusedArguments]
lemma lie_f_pow_toEnd_f (P : HasPrimitiveVectorWith t m μ) (n : ℕ) :
    ⁅f, ψ n⁆ = ψ (n + 1) := by
  simp [pow_succ']

variable (P : HasPrimitiveVectorWith t m μ)

include P

lemma lie_h_pow_toEnd_f (n : ℕ) :
    ⁅h, ψ n⁆ = (μ - 2 * n) • ψ n := by
  induction n with
  | zero => simpa using P.lie_h
  | succ n ih =>
    rw [pow_succ', LinearMap.mul_apply, toEnd_apply_apply, Nat.cast_add, Nat.cast_one,
      leibniz_lie h, t.lie_lie_smul_f R, ← neg_smul, ih, lie_smul, smul_lie, ← add_smul]
    congr
    ring

lemma lie_e_pow_succ_toEnd_f (n : ℕ) :
    ⁅e, ψ (n + 1)⁆ = ((n + 1) * (μ - n)) • ψ n := by
  induction n with
  | zero =>
      simp only [zero_add, pow_one, toEnd_apply_apply, Nat.cast_zero, sub_zero, one_mul,
        pow_zero, LinearMap.one_apply, leibniz_lie e, t.lie_e_f, P.lie_e, P.lie_h, lie_zero,
        add_zero]
  | succ n ih =>
    rw [pow_succ', LinearMap.mul_apply, toEnd_apply_apply, leibniz_lie e, t.lie_e_f,
      lie_h_pow_toEnd_f P, ih, lie_smul, lie_f_pow_toEnd_f P, ← add_smul,
      Nat.cast_add, Nat.cast_one]
    congr
    ring

lemma exists_nat [IsNoetherian R M] [NoZeroSMulDivisors R M] [IsDomain R] [CharZero R] :
    ∃ n : ℕ, μ = n := by
  suffices ∃ n : ℕ, (ψ n) = 0 by
    obtain ⟨n, hn₁, hn₂⟩ := Nat.exists_not_and_succ_of_not_zero_of_exists P.ne_zero this
    refine ⟨n, ?_⟩
    have := lie_e_pow_succ_toEnd_f P n
    rw [hn₂, lie_zero, eq_comm, smul_eq_zero_iff_left hn₁, mul_eq_zero, sub_eq_zero] at this
    exact this.resolve_left <| Nat.cast_add_one_ne_zero n
  have hs : (range <| fun (n : ℕ) ↦ μ - 2 * n).Infinite := by
    rw [infinite_range_iff (fun n m ↦ by simp)]; infer_instance
  by_contra! contra
  exact hs ((toEnd R L M h).eigenvectors_linearIndependent
    {μ - 2 * n | n : ℕ}
    (fun ⟨s, hs⟩ ↦ ψ Classical.choose hs)
    (fun ⟨r, hr⟩ ↦ by simp [lie_h_pow_toEnd_f P, Classical.choose_spec hr, contra,
      Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff])).finite

-- DISSOLVED: pow_toEnd_f_ne_zero_of_eq_nat

lemma pow_toEnd_f_eq_zero_of_eq_nat
    [IsNoetherian R M] [NoZeroSMulDivisors R M] [IsDomain R] [CharZero R]
    {n : ℕ} (hn : μ = n) : (ψ (n + 1)) = 0 := by
  by_contra h
  have : t.HasPrimitiveVectorWith (ψ (n + 1)) (n - 2 * (n + 1) : R) :=
    { ne_zero := h
      lie_h := (P.lie_h_pow_toEnd_f _).trans (by simp [hn])
      lie_e := (P.lie_e_pow_succ_toEnd_f _).trans (by simp [hn]) }
  obtain ⟨m, hm⟩ := this.exists_nat
  have : (n : ℤ) < m + 2 * (n + 1) := by omega
  exact this.ne (Int.cast_injective (α := R) <| by simpa [sub_eq_iff_eq_add] using hm)

end HasPrimitiveVectorWith

end IsSl2Triple
