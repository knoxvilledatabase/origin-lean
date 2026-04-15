/-
Extracted from RepresentationTheory/Homological/GroupHomology/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The group homology of a `k`-linear `G`-representation

Let `k` be a commutative ring and `G` a group. This file defines the group homology of
`A : Rep k G` to be the homology of the complex
$$\dots \to \bigoplus_{G^2} A \to \bigoplus_{G^1} A \to \bigoplus_{G^0} A$$
with differential $d_n$ sending $a\cdot (g_0, \dots, g_n)$ to
$$\rho(g_0^{-1})(a)\cdot (g_1, \dots, g_n)$$
$$+ \sum_{i = 0}^{n - 1}(-1)^{i + 1}a\cdot (g_0, \dots, g_ig_{i + 1}, \dots, g_n)$$
$$+ (-1)^{n + 1}a\cdot (g_0, \dots, g_{n - 1})$$ (where `ρ` is the representation attached to `A`).

We have a `k`-linear isomorphism
$\bigoplus_{G^n} A \cong (A \otimes_k \left(\bigoplus_{G^n} k[G]\right))_G$ given by
`Rep.coinvariantsTensorFreeLEquiv`. If we conjugate the $n$th differential in $(A \otimes_k P)_G$
by this isomorphism, where `P` is the bar resolution of `k` as a trivial `k`-linear
`G`-representation, then the resulting map agrees with the differential $d_n$ defined
above, a fact we prove.

Hence our $d_n$ squares to zero, and we get
$\mathrm{H}_n(G, A) \cong \mathrm{Tor}_n(A, k),$ where $\mathrm{Tor}$ is defined by deriving the
second argument of the functor $(A, B) \mapsto (A \otimes_k B)_G.$

To talk about homology in low degree, the file
`Mathlib/RepresentationTheory/Homological/GroupHomology/LowDegree.lean` provides API specialized to
`H₀`, `H₁`, `H₂`.

## Main definitions

* `Rep.Tor k G n`: the left-derived functors given by deriving the second argument of
  $(A, B) \mapsto (A \otimes_k B)_G$.
* `groupHomology.inhomogeneousChains A`: a complex whose objects are
  $\bigoplus_{G^n} A$ and whose homology is the group homology $\mathrm{H}_n(G, A).$
* `groupHomology.inhomogeneousChainsIso A`: an isomorphism between the above two complexes.
* `groupHomology A n`: this is $\mathrm{H}_n(G, A),$ defined as the $n$th homology of the
  second complex, `inhomogeneousChains A`.
* `groupHomologyIsoTor A n`: an isomorphism $\mathrm{H}_n(G, A) \cong \mathrm{Tor}_n(A, k)$
  induced by `inhomogeneousChainsIso A`.

## Implementation notes

Group homology is typically stated for `G`-modules, or equivalently modules over the group ring
`ℤ[G].` However, `ℤ` can be generalized to any commutative ring `k`, which is what we use.
Moreover, we express `k[G]`-module structures on a module `k`-module `A` using the `Rep` definition.
We avoid using instances `Module k[G] A` so that we do not run into possible scalar action diamonds.

Note that the existing definition of `Tor` in `Mathlib.CategoryTheory.Monoidal.Tor` is for monoidal
categories, and the bifunctor we need to derive here maps to `ModuleCat k`. Hence we define
`Rep.Tor k G n` by instead left-deriving the second argument of `Rep.coinvariantsTensor k G`:
$(A, B) \mapsto (A \otimes_k B)_G$. The functor `Rep.coinvariantsTensor k G` is naturally
isomorphic to the functor sending `A, B` to `A ⊗[k[G]] B`, where we give `A` the `k[G]ᵐᵒᵖ`-module
structure defined by `g • a := A.ρ g⁻¹ a`, but currently mathlib's `TensorProduct` is only defined
for commutative rings.

## TODO

* Upgrading `groupHomologyIsoTor` to an isomorphism of derived functors.

-/

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits

variable (k G : Type u) [CommRing k] [Group G]

open MonoidalCategory Representation Finsupp

section Tor

variable {k G} in

abbrev HomologicalComplex.coinvariantsTensorObj {α : Type*} [AddRightCancelSemigroup α] [One α]
    (A : Rep k G) (P : ChainComplex (Rep k G) α) :
    ChainComplex (ModuleCat k) α :=
  (((Rep.coinvariantsTensor k G).obj A).mapHomologicalComplex _).obj P

namespace Rep
