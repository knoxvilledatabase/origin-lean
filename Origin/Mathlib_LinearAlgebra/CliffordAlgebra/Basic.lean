/-
Extracted from LinearAlgebra/CliffordAlgebra/Basic.lean
Genuine: 3 of 6 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Clifford Algebras

We construct the Clifford algebra of a module `M` over a commutative ring `R`, equipped with
a quadratic form `Q`.

## Notation

The Clifford algebra of the `R`-module `M` equipped with a quadratic form `Q` is
an `R`-algebra denoted `CliffordAlgebra Q`.

Given a linear morphism `f : M → A` from a module `M` to another `R`-algebra `A`, such that
`cond : ∀ m, f m * f m = algebraMap _ _ (Q m)`, there is a (unique) lift of `f` to an `R`-algebra
morphism from `CliffordAlgebra Q` to `A`, which is denoted `CliffordAlgebra.lift Q f cond`.

The canonical linear map `M → CliffordAlgebra Q` is denoted `CliffordAlgebra.ι Q`.

## Theorems

The main theorems proved ensure that `CliffordAlgebra Q` satisfies the universal property
of the Clifford algebra.
1. `ι_comp_lift` is the fact that the composition of `ι Q` with `lift Q f cond` agrees with `f`.
2. `lift_unique` ensures the uniqueness of `lift Q f cond` with respect to 1.

## Implementation details

The Clifford algebra of `M` is constructed as a quotient of the tensor algebra, as follows.
1. We define a relation `CliffordAlgebra.Rel Q` on `TensorAlgebra R M`.
   This is the smallest relation which identifies squares of elements of `M` with `Q m`.
2. The Clifford algebra is the quotient of the tensor algebra by this relation.

This file is almost identical to `Mathlib/LinearAlgebra/ExteriorAlgebra/Basic.lean`.
-/

variable {R : Type*} [CommRing R]

variable {M : Type*} [AddCommGroup M] [Module R M]

variable (Q : QuadraticForm R M)

namespace CliffordAlgebra

open TensorAlgebra

inductive Rel : TensorAlgebra R M → TensorAlgebra R M → Prop
  | of (m : M) : Rel (ι R m * ι R m) (algebraMap R _ (Q m))

end CliffordAlgebra

def CliffordAlgebra :=
  RingQuot (CliffordAlgebra.Rel Q)

deriving Inhabited, Ring, Algebra R

namespace CliffordAlgebra

-- INSTANCE (free from Core): (priority

example : (Semiring.toNatAlgebra : Algebra ℕ (CliffordAlgebra Q)) = instAlgebra' _ := rfl

example : (Ring.toIntAlgebra _ : Algebra ℤ (CliffordAlgebra Q)) = instAlgebra' _ := rfl

-- INSTANCE (free from Core): {R

-- INSTANCE (free from Core): {R

def ι : M →ₗ[R] CliffordAlgebra Q :=
  (RingQuot.mkAlgHom R _).toLinearMap.comp (TensorAlgebra.ι R)
