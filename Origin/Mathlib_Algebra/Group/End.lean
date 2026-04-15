/-
Extracted from Algebra/Group/End.lean
Genuine: 1 of 8 | Dissolved: 0 | Infrastructure: 7
-/
import Origin.Core

/-!
# Monoids of endomorphisms, groups of automorphisms

This file defines
* the endomorphism monoid structure on `Function.End α := α → α`
* the endomorphism monoid structure on `Monoid.End M := M →* M` and `AddMonoid.End M := M →+ M`
* the automorphism group structure on `Equiv.Perm α := α ≃ α`
* the automorphism group structure on `MulAut M := M ≃* M` and `AddAut M := M ≃+ M`.

## Implementation notes

The definition of multiplication in the endomorphism monoids and automorphism groups agrees with
function composition, and multiplication in `CategoryTheory.End`, but not with
`CategoryTheory.comp`.

## Tags

end monoid, aut group
-/

assert_not_exists HeytingAlgebra MonoidWithZero MulAction RelIso

variable {A M G α β γ : Type*}

/-! ### Type endomorphisms -/

variable (α) in

protected def Function.End := α → α

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

/-! ### Monoid endomorphisms -/

namespace Equiv.Perm

attribute [to_additive_dont_translate] Perm

-- INSTANCE (free from Core): instOne

-- INSTANCE (free from Core): instMul

-- INSTANCE (free from Core): instInv

-- INSTANCE (free from Core): instPowNat

-- INSTANCE (free from Core): permGroup
