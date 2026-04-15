/-
Extracted from Order/Heyting/Hom.lean
Genuine: 6 of 14 | Dissolved: 0 | Infrastructure: 8
-/
import Origin.Core

/-!
# Heyting algebra morphisms

A Heyting homomorphism between two Heyting algebras is a bounded lattice homomorphism that preserves
Heyting implication.

We use the `DFunLike` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `HeytingHom`: Heyting homomorphisms.
* `CoheytingHom`: Co-Heyting homomorphisms.
* `BiheytingHom`: Bi-Heyting homomorphisms.

## Typeclasses

* `HeytingHomClass`
* `CoheytingHomClass`
* `BiheytingHomClass`
-/

open Function

variable {F α β γ δ : Type*}

structure HeytingHom (α β : Type*) [HeytingAlgebra α] [HeytingAlgebra β] extends
  LatticeHom α β where
  /-- The proposition that a Heyting homomorphism preserves the bottom element. -/
  protected map_bot' : toFun ⊥ = ⊥
  /-- The proposition that a Heyting homomorphism preserves the Heyting implication. -/
  protected map_himp' : ∀ a b, toFun (a ⇨ b) = toFun a ⇨ toFun b

structure CoheytingHom (α β : Type*) [CoheytingAlgebra α] [CoheytingAlgebra β] extends
  LatticeHom α β where
  /-- The proposition that a co-Heyting homomorphism preserves the top element. -/
  protected map_top' : toFun ⊤ = ⊤
  /-- The proposition that a co-Heyting homomorphism preserves the difference operation. -/
  protected map_sdiff' : ∀ a b, toFun (a \ b) = toFun a \ toFun b

structure BiheytingHom (α β : Type*) [BiheytingAlgebra α] [BiheytingAlgebra β] extends
  LatticeHom α β where
  /-- The proposition that a bi-Heyting homomorphism preserves the Heyting implication. -/
  protected map_himp' : ∀ a b, toFun (a ⇨ b) = toFun a ⇨ toFun b
  /-- The proposition that a bi-Heyting homomorphism preserves the difference operation. -/
  protected map_sdiff' : ∀ a b, toFun (a \ b) = toFun a \ toFun b

class HeytingHomClass (F α β : Type*) [HeytingAlgebra α] [HeytingAlgebra β] [FunLike F α β] : Prop
    extends LatticeHomClass F α β where
  /-- The proposition that a Heyting homomorphism preserves the bottom element. -/
  map_bot (f : F) : f ⊥ = ⊥
  /-- The proposition that a Heyting homomorphism preserves the Heyting implication. -/
  map_himp (f : F) : ∀ a b, f (a ⇨ b) = f a ⇨ f b

class CoheytingHomClass (F α β : Type*) [CoheytingAlgebra α] [CoheytingAlgebra β] [FunLike F α β] :
    Prop
  extends LatticeHomClass F α β where
  /-- The proposition that a co-Heyting homomorphism preserves the top element. -/
  map_top (f : F) : f ⊤ = ⊤
  /-- The proposition that a co-Heyting homomorphism preserves the difference operation. -/
  map_sdiff (f : F) : ∀ a b, f (a \ b) = f a \ f b

class BiheytingHomClass (F α β : Type*) [BiheytingAlgebra α] [BiheytingAlgebra β] [FunLike F α β] :
    Prop
  extends LatticeHomClass F α β where
  /-- The proposition that a bi-Heyting homomorphism preserves the Heyting implication. -/
  map_himp (f : F) : ∀ a b, f (a ⇨ b) = f a ⇨ f b
  /-- The proposition that a bi-Heyting homomorphism preserves the difference operation. -/
  map_sdiff (f : F) : ∀ a b, f (a \ b) = f a \ f b

export HeytingHomClass (map_himp)

export CoheytingHomClass (map_sdiff)

attribute [simp] map_himp map_sdiff

section Hom

variable [FunLike F α β]

/-! This section passes in some instances implicitly. See note [implicit instance arguments] -/

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

end Hom

section Equiv

variable [EquivLike F α β]

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

end Equiv

variable [FunLike F α β]

-- INSTANCE (free from Core): BoundedLatticeHomClass.toBiheytingHomClass

section HeytingAlgebra

open scoped symmDiff

variable [HeytingAlgebra α] [HeytingAlgebra β] [HeytingHomClass F α β] (f : F)
