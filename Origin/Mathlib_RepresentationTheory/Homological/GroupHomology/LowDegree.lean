/-
Extracted from RepresentationTheory/Homological/GroupHomology/LowDegree.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The low-degree homology of a `k`-linear `G`-representation

Let `k` be a commutative ring and `G` a group. This file contains specialised API for
the cycles and group homology of a `k`-linear `G`-representation `A` in degrees 0, 1 and 2.
In `Mathlib/RepresentationTheory/Homological/GroupHomology/Basic.lean`, we define the `n`th group
homology of `A` to be the homology of a complex `inhomogeneousChains A`, whose objects are
`(Fin n →₀ G) → A`; this is unnecessarily unwieldy in low degree.

Given an additive abelian group `A` with an appropriate scalar action of `G`, we provide support
for turning a finsupp `f : G →₀ A` satisfying the 1-cycle identity into an element of the
`cycles₁` of the representation on `A` corresponding to the scalar action. We also do this for
0-boundaries, 1-boundaries, 2-cycles and 2-boundaries.

The file also contains an identification between the definitions in
`Mathlib/RepresentationTheory/Homological/GroupHomology/Basic.lean`, `groupHomology.cycles A n`, and
the `cyclesₙ` in this file for `n = 1, 2`, as well as an isomorphism
`groupHomology.cycles A 0 ≅ A.V`.
Moreover, we provide API for the natural maps `cyclesₙ A → Hn A` for `n = 1, 2`.

We show that when the representation on `A` is trivial, `H₁(G, A) ≃+ Gᵃᵇ ⊗[ℤ] A`.

## Main definitions

* `groupHomology.H0Iso A`: isomorphism between `H₀(G, A)` and the coinvariants `A_G` of the
  `G`-representation on `A`.
* `groupHomology.H1π A`: epimorphism from the 1-cycles (i.e. `Z₁(G, A) := Ker(d₀ : (G →₀ A) → A`)
  to `H₁(G, A)`.
* `groupHomology.H2π A`: epimorphism from the 2-cycles
  (i.e. `Z₂(G, A) := Ker(d₁ : (G² →₀ A) → (G →₀ A)`) to `H₂(G, A)`.
* `groupHomology.H1AddEquivOfIsTrivial`: an isomorphism `H₁(G, A) ≃+ Gᵃᵇ ⊗[ℤ] A` when the
  representation on `A` is trivial.

-/

universe v u

noncomputable section

open CategoryTheory Limits Representation Rep Finsupp

variable {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G)

namespace groupHomology

section Chains

def chainsIso₀ : (inhomogeneousChains A).X 0 ≅ ModuleCat.of k A.V :=
  (LinearEquiv.finsuppUnique _ _ _).toModuleIso

def chainsIso₁ : (inhomogeneousChains A).X 1 ≅ ModuleCat.of k (G →₀ A) :=
  (Finsupp.domLCongr (Equiv.funUnique (Fin 1) G)).toModuleIso

def chainsIso₂ : (inhomogeneousChains A).X 2 ≅ ModuleCat.of k (G × G →₀ A) :=
  (Finsupp.domLCongr (piFinTwoEquiv fun _ => G)).toModuleIso

def chainsIso₃ : (inhomogeneousChains A).X 3 ≅ ModuleCat.of k (G × G × G →₀ A) :=
  (Finsupp.domLCongr ((Fin.consEquiv _).symm.trans
    ((Equiv.refl G).prodCongr (piFinTwoEquiv fun _ => G)))).toModuleIso

end Chains

section Differentials

def d₁₀ : ModuleCat.of k (G →₀ A) ⟶ ModuleCat.of k A.V :=
  ModuleCat.ofHom <| lsum k fun g => A.ρ g⁻¹ - LinearMap.id
