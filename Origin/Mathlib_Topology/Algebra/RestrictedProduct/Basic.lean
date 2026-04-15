/-
Extracted from Topology/Algebra/RestrictedProduct/Basic.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Restricted products of sets, groups and rings

We define the **restricted product** of `R : ι → Type*` of types, relative to
a family of subsets `A : (i : ι) → Set (R i)` and a filter `𝓕 : Filter ι`. This
is the set of all `x : Π i, R i` such that the set `{j | x j ∈ A j}` belongs to `𝓕`.
We denote it by `Πʳ i, [R i, A i]_[𝓕]`.

The main case of interest, which we shall refer to as the "classical restricted product",
is that of `𝓕 = cofinite`. Recall that this is the filter of all subsets of `ι`, which are
*cofinite* in the sense that they have finite complement.
Hence, the associated restricted product is the set of all `x : Π i, R i` such that
`x j ∈ A j` for all but finitely many `j`s. We denote it simply by `Πʳ i, [R i, A i]`.

Another notable case is that of the principal filter `𝓕 = 𝓟 s` corresponding to some subset `s`
of `ι`. The associated restricted product `Πʳ i, [R i, A i]_[𝓟 s]` is the set of all
`x : Π i, R i` such that `x j ∈ A j` for all `j ∈ s`. Put another way, this is just
`(Π i ∈ s, A i) × (Π i ∉ s, R i)`, modulo the obvious isomorphism.

We endow these types with the obvious algebraic structures. We also show various compatibility
results.

See also the file `Mathlib/Topology/Algebra/RestrictedProduct/TopologicalSpace.lean`, which
puts the structure of a topological space on a restricted product of topological spaces.

## Main definitions

* `RestrictedProduct`: the restricted product of a family `R` of types, relative to a family `A` of
  subsets and a filter `𝓕` on the indexing set. This is denoted `Πʳ i, [R i, A i]_[𝓕]`,
  or simply `Πʳ i, [R i, A i]` when `𝓕 = cofinite`.
* `RestrictedProduct.instDFunLike`: interpret an element of `Πʳ i, [R i, A i]_[𝓕]` as an element
  of `Π i, R i` using the `DFunLike` machinery.
* `RestrictedProduct.structureMap`: the inclusion map from `Π i, A i` to `Πʳ i, [R i, A i]_[𝓕]`.

## Notation

* `Πʳ i, [R i, A i]_[𝓕]` is `RestrictedProduct R A 𝓕`.
* `Πʳ i, [R i, A i]` is `RestrictedProduct R A cofinite`.

## Tags

restricted product, adeles, ideles
-/

open Set Filter

variable {ι : Type*}

variable (R : ι → Type*) (A : (i : ι) → Set (R i))

/-!
## Definition and elementary maps
-/

def RestrictedProduct (𝓕 : Filter ι) : Type _ := {x : Π i, R i // ∀ᶠ i in 𝓕, x i ∈ A i}

open Batteries.ExtendedBinder

scoped[RestrictedProduct]

notation3 "Πʳ " (...) ", " "[" r:(scoped R => R)", " a:(scoped A => A) "]_[" f "]" =>

  RestrictedProduct r a f

scoped[RestrictedProduct]

notation3 "Πʳ " (...) ", " "[" r:(scoped R => R)", " a:(scoped A => A) "]" =>

  RestrictedProduct r a cofinite

namespace RestrictedProduct

open scoped RestrictedProduct

variable {𝓕 𝓖 : Filter ι}

-- INSTANCE (free from Core): :

variable {R A} in

abbrev mk (x : Π i, R i) (hx : ∀ᶠ i in 𝓕, x i ∈ A i) : Πʳ i, [R i, A i]_[𝓕] :=
  ⟨x, hx⟩
