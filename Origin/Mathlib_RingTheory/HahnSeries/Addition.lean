/-
Extracted from RingTheory/HahnSeries/Addition.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Additive properties of Hahn series
If `Γ` is ordered and `R` has zero, then `R⟦Γ⟧` consists of formal series over `Γ` with coefficients
in `R`, whose supports are partially well-ordered. With further structure on `R` and `Γ`, we can add
further structure on `R⟦Γ⟧`.  When `R` has an addition operation, `R⟦Γ⟧` also has addition by adding
coefficients.

## Main Definitions
* If `R` is a (commutative) additive monoid or group, then so is `R⟦Γ⟧`.

## References
- [J. van der Hoeven, *Operators on Generalized Power Series*][van_der_hoeven]
-/

open Finset Function

noncomputable section

variable {Γ Γ' R S U V α : Type*}

namespace HahnSeries

section SMulZeroClass

variable [PartialOrder Γ] {V : Type*} [Zero V] [SMulZeroClass R V]

-- INSTANCE (free from Core): :

theorem support_smul_subset (r : R) (x : HahnSeries Γ V) : (r • x).support ⊆ x.support :=
  Function.support_const_smul_subset ..
