/-
Extracted from LinearAlgebra/LinearPMap.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Partially defined linear maps

A `LinearPMap σ E F` or `E →ₛₗ.[σ] F` is a semilinear map from a submodule of `E` to `F` with a ring
homomorphism `σ` between the scalars. This reduces to a linear map when `σ` is the identity.
We define a `SemilatticeInf` with `OrderBot` instance on this, and define three operations:

* `mkSpanSingleton` defines a partial linear map defined on the span of a singleton.
* `sup` takes two partial linear maps `f`, `g` that agree on the intersection of their
  domains, and returns the unique partial linear map on `f.domain ⊔ g.domain` that
  extends both `f` and `g`.
* `sSup` takes a `DirectedOn (· ≤ ·)` set of partial linear maps, and returns the unique
  partial linear map on the `sSup` of their domains that extends all these maps.

Moreover, we define
* `LinearPMap.graph` is the graph of the partial linear map viewed as a submodule of `E × F`.
TODO: This should be also generalized to semilinear maps, but one has to define a new type where `R`
acts on `E` normally while `R` acts on `F` through `σ`.

Partially defined maps are currently used in `Mathlib` to prove the Hahn-Banach theorem
and its variations. Namely, `LinearPMap.sSup` implies that every chain of `LinearPMap`s
is bounded above.
They are also the basis for the theory of unbounded operators.

-/

structure LinearPMap {R S : Type*} [Ring R] [Ring S] (σ : R →+* S) (E : Type*)
    [AddCommGroup E] [Module R E] (F : Type*) [AddCommGroup F] [Module S F] where
  /-- The domain of the (semi)linear map. -/
  domain : Submodule R E
  /-- The (semi)linear map itself. -/
  toFun : domain →ₛₗ[σ] F
