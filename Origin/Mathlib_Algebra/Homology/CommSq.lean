/-
Extracted from Algebra/Homology/CommSq.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Relation between pullback/pushout squares and kernel/cokernel sequences

Consider a commutative square in a preadditive category:

```
X₁ ⟶ X₂
|    |
v    v
X₃ ⟶ X₄
```

In this file, we show that this is a pushout square iff the object `X₄`
identifies to the cokernel of the difference map `X₁ ⟶ X₂ ⊞ X₃`
via the obvious map `X₂ ⊞ X₃ ⟶ X₄`.

Similarly, it is a pullback square iff the object `X₁`
identifies to the kernel of the difference map `X₂ ⊞ X₃ ⟶ X₄`
via the obvious map `X₁ ⟶ X₂ ⊞ X₃`.

-/

namespace CategoryTheory

open Category Limits

variable {C : Type*} [Category* C] [Preadditive C]
  {X₁ X₂ X₃ X₄ : C} [HasBinaryBiproduct X₂ X₃]

section Pushout

variable {f : X₁ ⟶ X₂} {g : X₁ ⟶ X₃} {inl : X₂ ⟶ X₄} {inr : X₃ ⟶ X₄}

noncomputable abbrev CommSq.cokernelCofork (sq : CommSq f g inl inr) :
    CokernelCofork (biprod.lift f (-g)) :=
  CokernelCofork.ofπ (biprod.desc inl inr) (by simp [sq.w])
