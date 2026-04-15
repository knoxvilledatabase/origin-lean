/-
Extracted from Algebra/Lie/Abelian.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Trivial Lie modules and Abelian Lie algebras

The action of a Lie algebra `L` on a module `M` is trivial if `⁅x, m⁆ = 0` for all `x ∈ L` and
`m ∈ M`. In the special case that `M = L` with the adjoint action, triviality corresponds to the
concept of an Abelian Lie algebra.

In this file we define these concepts and provide some related definitions and results.

## Main definitions

  * `LieModule.IsTrivial`
  * `IsLieAbelian`
  * `isMulCommutative_iff_isLieAbelian`
  * `LieModule.ker`
  * `LieModule.maxTrivSubmodule`
  * `LieAlgebra.center`

## Tags

lie algebra, abelian, commutative, center
-/

universe u v w w₁ w₂

class LieModule.IsTrivial (L : Type v) (M : Type w) [Bracket L M] [Zero M] : Prop where
  trivial : ∀ (x : L) (m : M), ⁅x, m⁆ = 0
