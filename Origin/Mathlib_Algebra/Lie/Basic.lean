/-
Extracted from Algebra/Lie/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lie algebras

This file defines Lie rings and Lie algebras over a commutative ring together with their
modules, morphisms and equivalences, as well as various lemmas to make these definitions usable.

## Main definitions

  * `LieRing`
  * `LieAlgebra`
  * `LieRingModule`
  * `LieModule`
  * `LieHom`
  * `LieEquiv`
  * `LieModuleHom`
  * `LieModuleEquiv`

## Notation

Working over a fixed commutative ring `R`, we introduce the notations:
* `L →ₗ⁅R⁆ L'` for a morphism of Lie algebras,
* `L ≃ₗ⁅R⁆ L'` for an equivalence of Lie algebras,
* `M →ₗ⁅R,L⁆ N` for a morphism of Lie algebra modules `M`, `N` over a Lie algebra `L`,
* `M ≃ₗ⁅R,L⁆ N` for an equivalence of Lie algebra modules `M`, `N` over a Lie algebra `L`.

## Implementation notes

Lie algebras are defined as modules with a compatible Lie ring structure and thus, like modules,
are partially unbundled.

## References
* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 1--3*](bourbaki1975)

## Tags

lie bracket, jacobi identity, lie ring, lie algebra, lie module
-/

universe u v w w₁ w₂

open Function

class LieRing (L : Type v) extends AddCommGroup L, Bracket L L where
  /-- A Lie ring bracket is additive in its first component. -/
  protected add_lie : ∀ x y z : L, ⁅x + y, z⁆ = ⁅x, z⁆ + ⁅y, z⁆
  /-- A Lie ring bracket is additive in its second component. -/
  protected lie_add : ∀ x y z : L, ⁅x, y + z⁆ = ⁅x, y⁆ + ⁅x, z⁆
  /-- A Lie ring bracket vanishes on the diagonal in L × L. -/
  protected lie_self : ∀ x : L, ⁅x, x⁆ = 0
  /-- A Lie ring bracket satisfies a Leibniz / Jacobi identity. -/
  protected leibniz_lie : ∀ x y z : L, ⁅x, ⁅y, z⁆⁆ = ⁅⁅x, y⁆, z⁆ + ⁅y, ⁅x, z⁆⁆
