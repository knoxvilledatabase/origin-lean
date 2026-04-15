/-
Extracted from CategoryTheory/Category/TwoP.lean
Genuine: 3 of 6 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# The category of two-pointed types

This defines `TwoP`, the category of two-pointed types.

## References

* [nLab, *coalgebra of the real interval*]
  (https://ncatlab.org/nlab/show/coalgebra+of+the+real+interval)
-/

open CategoryTheory Option

universe u

variable {α β : Type*}

structure TwoP : Type (u + 1) where
  /-- The underlying type of a two-pointed type. -/
  protected X : Type u
  /-- The two points of a bipointed type, bundled together as a pair of distinct elements. -/
  toTwoPointing : TwoPointing X

namespace TwoP

-- INSTANCE (free from Core): :

abbrev of {X : Type*} (toTwoPointing : TwoPointing X) : TwoP :=
  ⟨X, toTwoPointing⟩

alias _root_.TwoPointing.TwoP := of

-- INSTANCE (free from Core): :

noncomputable def toBipointed (X : TwoP) : Bipointed :=
  X.toTwoPointing.toProd.Bipointed
