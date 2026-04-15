/-
Extracted from RingTheory/FreeRing.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Free rings

The theory of the free ring over a type.

## Main definitions

* `FreeRing α` : the free (not commutative in general) ring over a type.
* `lift (f : α → R)` : the ring hom `FreeRing α →+* R` induced by `f`.
* `map (f : α → β)` : the ring hom `FreeRing α →+* FreeRing β` induced by `f`.

## Implementation details

`FreeRing α` is implemented as the free abelian group over the free monoid on `α`.

## Tags

free ring

-/

universe u v

def FreeRing (α : Type u) : Type u :=
  FreeAbelianGroup <| FreeMonoid α

deriving Ring, Inhabited, Nontrivial

namespace FreeRing

variable {α : Type u}

def of (x : α) : FreeRing α :=
  FreeAbelianGroup.of (FreeMonoid.of x)

theorem of_injective : Function.Injective (of : α → FreeRing α) :=
  FreeAbelianGroup.of_injective.comp FreeMonoid.of_injective
