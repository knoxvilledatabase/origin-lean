/-
Extracted from Algebra/AffineMonoid/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Affine monoids

This file defines affine monoids as finitely generated cancellative torsion-free commutative
monoids.
-/

class abbrev IsAffineAddMonoid (M : Type*) [AddCommMonoid M] : Prop :=
  IsCancelAdd M, AddMonoid.FG M, IsAddTorsionFree M
