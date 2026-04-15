/-
Extracted from Algebra/Group/TypeTags/Basic.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Type tags that turn additive structures into multiplicative, and vice versa

We define two type tags:

* `Additive α`: turns any multiplicative structure on `α` into the corresponding
  additive structure on `Additive α`;
* `Multiplicative α`: turns any additive structure on `α` into the corresponding
  multiplicative structure on `Multiplicative α`.

We also define instances `Additive.*` and `Multiplicative.*` that actually transfer the structures.

## See also

This file is similar to `Mathlib/Order/Synonym.lean`.

-/

assert_not_exists MonoidWithZero DenselyOrdered MonoidHom Finite

universe u v

variable {α : Type u} {β : Type v}

def Additive (α : Type*) := α

def Multiplicative (α : Type*) := α

namespace Additive

def ofMul : α ≃ Additive α :=
  ⟨fun x => x, fun x => x, fun _ => rfl, fun _ => rfl⟩

def toMul : Additive α ≃ α := ofMul.symm
