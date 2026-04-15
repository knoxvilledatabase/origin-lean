/-
Extracted from NumberTheory/Cyclotomic/PrimitiveRoots.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Primitive roots in cyclotomic fields
If `IsCyclotomicExtension {n} A B`, we define an element `zeta n A B : B` that is a primitive
`n`th-root of unity in `B` and we study its properties. We also prove related theorems under the
more general assumption of just being a primitive root, for reasons described in the implementation
details section.

## Main definitions
* `IsCyclotomicExtension.zeta n A B`: if `IsCyclotomicExtension {n} A B`, then `zeta n A B`
  is a primitive `n`-th root of unity in `B`.
* `IsPrimitiveRoot.powerBasis`: if `K` and `L` are fields such that
  `IsCyclotomicExtension {n} K L`, then `IsPrimitiveRoot.powerBasis`
  gives a `K`-power basis for `L` given a primitive root `ζ`.
* `IsPrimitiveRoot.embeddingsEquivPrimitiveRoots`: the equivalence between `L →ₐ[K] A`
  and `primitiveRoots n A` given by the choice of `ζ`.

## Main results
* `IsCyclotomicExtension.zeta_spec`: `zeta n A B` is a primitive `n`-th root of unity.
* `IsCyclotomicExtension.finrank`: if `Irreducible (cyclotomic n K)` (in particular for
  `K = ℚ`), then the `finrank` of a cyclotomic extension is `n.totient`.
* `IsPrimitiveRoot.norm_eq_one`: if `Irreducible (cyclotomic n K)` (in particular for `K = ℚ`),
  the norm of a primitive root is `1` if `n ≠ 2`.
* `IsPrimitiveRoot.sub_one_norm_eq_eval_cyclotomic`: if `Irreducible (cyclotomic n K)`
  (in particular for `K = ℚ`), then the norm of `ζ - 1` is `eval 1 (cyclotomic n ℤ)`, for a
  primitive root `ζ`. We also prove the analogous of this result for `zeta`.
* `IsPrimitiveRoot.norm_pow_sub_one_of_prime_pow_ne_two` : if
  `Irreducible (cyclotomic (p ^ (k + 1)) K)` (in particular for `K = ℚ`) and `p` is a prime,
  then the norm of `ζ ^ (p ^ s) - 1` is `p ^ (p ^ s)` `p ^ (k - s + 1) ≠ 2`. See the following
  lemmas for similar results. We also prove the analogous of this result for `zeta`.
* `IsPrimitiveRoot.norm_sub_one_of_prime_ne_two` : if `Irreducible (cyclotomic (p ^ (k + 1)) K)`
  (in particular for `K = ℚ`) and `p` is an odd prime, then the norm of `ζ - 1` is `p`. We also
  prove the analogous of this result for `zeta`.
* `IsPrimitiveRoot.embeddingsEquivPrimitiveRoots`: the equivalence between `L →ₐ[K] A`
  and `primitiveRoots n A` given by the choice of `ζ`.

## Implementation details
`zeta n A B` is defined as any primitive root of unity in `B`, - this must exist, by definition of
`IsCyclotomicExtension`. It is not true in general that it is a root of `cyclotomic n B`,
but this holds if `isDomain B` and `NeZero (n : B)`.

`zeta n A B` is defined using `Exists.choose`, which means we cannot control it.
For example, in normal mathematics, we can demand that `(zeta p ℤ ℤ[ζₚ] : ℚ(ζₚ))` is equal to
`zeta p ℚ ℚ(ζₚ)`, as we are just choosing "an arbitrary primitive root" and we can internally
specify that our choices agree. This is not the case here, and it is indeed impossible to prove that
these two are equal. Therefore, whenever possible, we prove our results for any primitive root,
and only at the "final step", when we need to provide an "explicit" primitive root, we use `zeta`.

-/

open Polynomial Algebra Finset Module IsCyclotomicExtension Nat PNat Set

open scoped IntermediateField

universe u v w z

variable {p n : ℕ} [NeZero n] (A : Type w) (B : Type z) (K : Type u) {L : Type v} (C : Type w)

variable [CommRing A] [CommRing B] [Algebra A B] [IsCyclotomicExtension {n} A B]

section Zeta

namespace IsCyclotomicExtension

variable (n)

noncomputable def zeta : B :=
  (exists_isPrimitiveRoot A B (Set.mem_singleton n) (NeZero.ne _) :
    ∃ r : B, IsPrimitiveRoot r n).choose
