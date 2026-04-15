/-
Extracted from Analysis/Normed/Ring/Basic.lean
Genuine: 9 of 22 | Dissolved: 0 | Infrastructure: 13
-/
import Origin.Core

/-!
# Normed rings

In this file we define (semi)normed rings. We also prove some theorems about these definitions.

A normed ring instance can be constructed from a given real absolute value on a ring via
`AbsoluteValue.toNormedRing`.
-/

assert_not_exists AddChar comap_norm_atTop DilationEquiv Finset.sup_mul_le_mul_sup_of_nonneg

  IsOfFinOrder Isometry.norm_map_of_map_one NNReal.isOpen_Ico_zero Rat.norm_cast_real

  RestrictScalars

variable {G α β ι : Type*}

open Filter

open scoped Topology NNReal

class NonUnitalSeminormedRing (α : Type*) extends Norm α, NonUnitalRing α,
  PseudoMetricSpace α where
  /-- The distance is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = norm (-x + y)
  /-- The norm is submultiplicative. -/
  protected norm_mul_le : ∀ a b, norm (a * b) ≤ norm a * norm b

class SeminormedRing (α : Type*) extends Norm α, Ring α, PseudoMetricSpace α where
  /-- The distance is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = norm (-x + y)
  /-- The norm is submultiplicative. -/
  norm_mul_le : ∀ a b, norm (a * b) ≤ norm a * norm b

-- INSTANCE (free from Core): (priority

class NonUnitalNormedRing (α : Type*) extends Norm α, NonUnitalRing α, MetricSpace α where
  /-- The distance is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = norm (-x + y)
  /-- The norm is submultiplicative. -/
  norm_mul_le : ∀ a b, norm (a * b) ≤ norm a * norm b

-- INSTANCE (free from Core): (priority

class NormedRing (α : Type*) extends Norm α, Ring α, MetricSpace α where
  /-- The distance is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = norm (-x + y)
  /-- The norm is submultiplicative. -/
  norm_mul_le : ∀ a b, norm (a * b) ≤ norm a * norm b

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

class NonUnitalSeminormedCommRing (α : Type*)
    extends NonUnitalSeminormedRing α, NonUnitalCommRing α where

-- INSTANCE (free from Core): 100]

class NonUnitalNormedCommRing (α : Type*) extends NonUnitalNormedRing α, NonUnitalCommRing α where

-- INSTANCE (free from Core): 100]

-- INSTANCE (free from Core): (priority

class SeminormedCommRing (α : Type*) extends SeminormedRing α, CommRing α where

-- INSTANCE (free from Core): 100]

class NormedCommRing (α : Type*) extends NormedRing α, CommRing α where

-- INSTANCE (free from Core): 100]

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): PUnit.normedCommRing

section NormOneClass

class NormOneClass (α : Type*) [Norm α] [One α] : Prop where
  /-- The norm of the multiplicative identity is 1. -/
  norm_one : ‖(1 : α)‖ = 1

export NormOneClass (norm_one)

attribute [simp] norm_one

section SeminormedAddCommGroup

variable [SeminormedAddCommGroup G] [One G] [NormOneClass G]
