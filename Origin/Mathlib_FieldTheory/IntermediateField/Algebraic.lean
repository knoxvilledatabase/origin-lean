/-
Extracted from FieldTheory/IntermediateField/Algebraic.lean
Genuine: 3 of 7 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Results on finite dimensionality and algebraicity of intermediate fields.
-/

open Module

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  {S : IntermediateField K L}

theorem IntermediateField.coe_isIntegral_iff {R : Type*} [CommRing R] [Algebra R K] [Algebra R L]
    [IsScalarTower R K L] {x : S} : IsIntegral R (x : L) ↔ IsIntegral R x :=
  isIntegral_algHom_iff (S.val.restrictScalars R) Subtype.val_injective

def Subalgebra.IsAlgebraic.toIntermediateField {S : Subalgebra K L} (hS : S.IsAlgebraic) :
    IntermediateField K L where
  toSubalgebra := S
  inv_mem' x hx := Algebra.adjoin_le_iff.mpr
    (Set.singleton_subset_iff.mpr hx) (hS x hx).isIntegral.inv_mem_adjoin

abbrev Algebra.IsAlgebraic.toIntermediateField (S : Subalgebra K L) [Algebra.IsAlgebraic K S] :
    IntermediateField K L := (S.isAlgebraic_iff.mpr ‹_›).toIntermediateField

namespace IntermediateField

-- INSTANCE (free from Core): isAlgebraic_tower_bot

-- INSTANCE (free from Core): isAlgebraic_tower_top

section FiniteDimensional

variable (F E : IntermediateField K L)

-- INSTANCE (free from Core): finiteDimensional_left

-- INSTANCE (free from Core): finiteDimensional_right
