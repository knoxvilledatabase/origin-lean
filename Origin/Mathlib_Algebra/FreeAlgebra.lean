/-
Extracted from Algebra/FreeAlgebra.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Free Algebras

Given a commutative semiring `R`, and a type `X`, we construct the free unital, associative
`R`-algebra on `X`.

## Notation

1. `FreeAlgebra R X` is the free algebra itself. It is endowed with an `R`-algebra structure.
2. `FreeAlgebra.ι R` is the function `X → FreeAlgebra R X`.
3. Given a function `f : X → A` to an R-algebra `A`, `lift R f` is the lift of `f` to an
   `R`-algebra morphism `FreeAlgebra R X → A`.

## Theorems

1. `ι_comp_lift` states that the composition `(lift R f) ∘ (ι R)` is identical to `f`.
2. `lift_unique` states that whenever an R-algebra morphism `g : FreeAlgebra R X → A` is
   given whose composition with `ι R` is `f`, then one has `g = lift R f`.
3. `hom_ext` is a variant of `lift_unique` in the form of an extensionality theorem.
4. `lift_comp_ι` is a combination of `ι_comp_lift` and `lift_unique`. It states that the lift
   of the composition of an algebra morphism with `ι` is the algebra morphism itself.
5. `equivMonoidAlgebraFreeMonoid : FreeAlgebra R X ≃ₐ[R] R[FreeMonoid X]`
6. An inductive principle `induction`.

## Implementation details

We construct the free algebra on `X` as a quotient of an inductive type `FreeAlgebra.Pre` by an
inductively defined relation `FreeAlgebra.Rel`. Explicitly, the construction involves three steps:
1. We construct an inductive type `FreeAlgebra.Pre R X`, the terms of which should be thought
   of as representatives for the elements of `FreeAlgebra R X`.
   It is the free type with maps from `R` and `X`, and with two binary operations `add` and `mul`.
2. We construct an inductive relation `FreeAlgebra.Rel R X` on `FreeAlgebra.Pre R X`.
   This is the smallest relation for which the quotient is an `R`-algebra where addition resp.
   multiplication are induced by `add` resp. `mul` from 1., and for which the map from `R` is the
   structure map for the algebra.
3. The free algebra `FreeAlgebra R X` is the quotient of `FreeAlgebra.Pre R X` by
   the relation `FreeAlgebra.Rel R X`.
-/

open scoped MonoidAlgebra

variable (R X : Type*) [CommSemiring R]

namespace FreeAlgebra

inductive Pre
  | of : X → Pre
  | ofScalar : R → Pre
  | add : Pre → Pre → Pre
  | mul : Pre → Pre → Pre

namespace Pre

-- INSTANCE (free from Core): :
