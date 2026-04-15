/-
Extracted from Order/Category/FinBoolAlg.lean
Genuine: 2 of 11 | Dissolved: 0 | Infrastructure: 9
-/
import Origin.Core

/-!
# The category of finite Boolean algebras

This file defines `FinBoolAlg`, the category of finite Boolean algebras.

## TODO

Birkhoff's representation for finite Boolean algebras.

```
FintypeCat_to_FinBoolAlg_op.left_op ⋙ FinBoolAlg.dual ≅
FintypeCat_to_FinBoolAlg_op.left_op
```

`FinBoolAlg` is essentially small.
-/

universe u

open CategoryTheory OrderDual Opposite

structure FinBoolAlg extends BoolAlg where
  [isFintype : Fintype toBoolAlg]

attribute [instance] FinBoolAlg.isFintype

namespace FinBoolAlg

-- INSTANCE (free from Core): :

abbrev of (α : Type*) [BooleanAlgebra α] [Fintype α] : FinBoolAlg where
  carrier := α

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): largeCategory

-- INSTANCE (free from Core): concreteCategory

-- INSTANCE (free from Core): hasForgetToBoolAlg

-- INSTANCE (free from Core): hasForgetToFinBddDistLat

-- INSTANCE (free from Core): forgetToBoolAlg_full

-- INSTANCE (free from Core): forgetToBoolAlgFaithful
