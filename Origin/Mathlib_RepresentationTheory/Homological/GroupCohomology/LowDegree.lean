/-
Extracted from RepresentationTheory/Homological/GroupCohomology/LowDegree.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The low-degree cohomology of a `k`-linear `G`-representation

Let `k` be a commutative ring and `G` a group. This file contains specialised API for
the cocycles and group cohomology of a `k`-linear `G`-representation `A` in degrees 0, 1 and 2.

In `Mathlib/RepresentationTheory/Homological/GroupCohomology/Basic.lean`, we define the `n`th group
cohomology of `A` to be the cohomology of a complex `inhomogeneousCochains A`, whose objects are
`(Fin n → G) → A`; this is unnecessarily unwieldy in low degree. Here, meanwhile, we define the one
and two cocycles and coboundaries as submodules of `Fun(G, A)` and `Fun(G × G, A)`, and provide
maps to `H1` and `H2`.

We also show that when the representation on `A` is trivial, `H¹(G, A) ≃ Hom(G, A)`.

Given an additive or multiplicative abelian group `A` with an appropriate scalar action of `G`,
we provide support for turning a function `f : G → A` satisfying the 1-cocycle identity into an
element of the `cocycles₁` of the representation on `A` (or `Additive A`) corresponding to the
scalar action. We also do this for 1-coboundaries, 2-cocycles and 2-coboundaries. The
multiplicative case, starting with the section `IsMulCocycle`, just mirrors the additive case;
unfortunately `@[to_additive]` can't deal with scalar actions.

The file also contains an identification between the definitions in
`Mathlib/RepresentationTheory/Homological/GroupCohomology/Basic.lean`,
`groupCohomology.cocycles A n`, and the `cocyclesₙ` in this file, for `n = 0, 1, 2`.

## Main definitions

* `groupCohomology.H0Iso A`: isomorphism between `H⁰(G, A)` and the invariants `Aᴳ` of the
  `G`-representation on `A`.
* `groupCohomology.H1π A`: epimorphism from the 1-cocycles
  (i.e. `Z¹(G, A) := Ker(d¹ : Fun(G, A) → Fun(G², A)`) to `H¹(G, A)`.
* `groupCohomology.H2π A`: epimorphism from the 2-cocycles
  (i.e. `Z²(G, A) := Ker(d² : Fun(G², A) → Fun(G³, A)`) to `H²(G, A)`.
* `groupCohomology.H1IsoOfIsTrivial`: the isomorphism `H¹(G, A) ≅ Hom(G, A)` when the
  representation on `A` is trivial.

## TODO

* The relationship between `H2` and group extensions
* Nonabelian group cohomology

-/

universe v u

noncomputable section

open CategoryTheory Limits Representation

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G)

namespace groupCohomology

section Cochains

def cochainsIso₀ : (inhomogeneousCochains A).X 0 ≅ ModuleCat.of k A.V :=
  (LinearEquiv.funUnique (Fin 0 → G) k A).toModuleIso

def cochainsIso₁ : (inhomogeneousCochains A).X 1 ≅ ModuleCat.of k (G → A) :=
  (LinearEquiv.funCongrLeft k A (Equiv.funUnique (Fin 1) G)).toModuleIso.symm

def cochainsIso₂ : (inhomogeneousCochains A).X 2 ≅ ModuleCat.of k (G × G → A) :=
  (LinearEquiv.funCongrLeft k A <| (piFinTwoEquiv fun _ => G)).toModuleIso.symm

def cochainsIso₃ : (inhomogeneousCochains A).X 3 ≅ ModuleCat.of k (G × G × G → A) :=
  (LinearEquiv.funCongrLeft k A <| ((Fin.consEquiv _).symm.trans
    ((Equiv.refl G).prodCongr (piFinTwoEquiv fun _ => G)))).toModuleIso.symm

end Cochains

section Differentials
