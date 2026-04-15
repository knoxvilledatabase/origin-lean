/-
Extracted from FieldTheory/Tower.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Finiteness of `IsScalarTower`

We prove that given `IsScalarTower F K A`, if `A` is finite as a module over `F` then
`A` is finite over `K`, and
(as long as `A` is Noetherian over `F` and torsion-free over `K`) `K` is finite over `F`.

In particular these conditions hold when `A`, `F`, and `K` are fields.

The formulas for the dimensions are given elsewhere by `Module.finrank_mul_finrank`.

## Tags

tower law

-/

universe u v w u₁ v₁ w₁

open Cardinal Submodule

variable (F : Type u) (K : Type v) (A : Type w)

namespace Module.Finite

variable [Ring F] [Ring K] [Module F K]
  [AddCommGroup A] [Module K A] [Module.IsTorsionFree K A]
  [Module F A] [IsNoetherian F A] [IsScalarTower F K A] in

theorem left [IsDomain K] [Nontrivial A] : Module.Finite F K :=
  let ⟨x, hx⟩ := exists_ne (0 : A)
  Module.Finite.of_injective
    (LinearMap.ringLmapEquivSelf K ℕ A |>.symm x |>.restrictScalars F) (smul_left_injective K hx)

variable [Semiring F] [Semiring K] [Module F K]
  [AddCommMonoid A] [Module K A] [Module F A] [IsScalarTower F K A] in
