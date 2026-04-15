/-
Extracted from Analysis/Normed/Field/Basic.lean
Genuine: 1 of 4 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Normed division rings and fields

In this file we define normed fields, and (more generally) normed division rings. We also prove
some theorems about these definitions.

Some useful results that relate the topology of the normed field to the discrete topology include:
* `norm_eq_one_iff_ne_zero_of_discrete`

Methods for constructing a normed field instance from a given real absolute value on a field are
given in:
* AbsoluteValue.toNormedField
-/

assert_not_exists AddChar comap_norm_atTop DilationEquiv Finset.sup_mul_le_mul_sup_of_nonneg

  IsOfFinOrder Isometry.norm_map_of_map_one NNReal.isOpen_Ico_zero Rat.norm_cast_real

  RestrictScalars

variable {G α β ι : Type*}

open Filter

open scoped Topology NNReal ENNReal

class NormedDivisionRing (α : Type*) extends Norm α, DivisionRing α, MetricSpace α where
  /-- The distance is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = norm (-x + y)
  /-- The norm is multiplicative. -/
  protected norm_mul : ∀ a b, norm (a * b) = norm a * norm b

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

section NormedDivisionRing

variable [NormedDivisionRing α] {a b : α}

-- INSTANCE (free from Core): (priority
