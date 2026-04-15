/-
Extracted from RepresentationTheory/Homological/GroupHomology/Functoriality.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Functoriality of group homology

Given a commutative ring `k`, a group homomorphism `f : G →* H`, a `k`-linear `G`-representation
`A`, a `k`-linear `H`-representation `B`, and a representation morphism `A ⟶ Res(f)(B)`, we get
a chain map `inhomogeneousChains A ⟶ inhomogeneousChains B` and hence maps on homology
`Hₙ(G, A) ⟶ Hₙ(H, B)`.

We also provide extra API for these maps in degrees 0, 1, 2.

## Main definitions

* `groupHomology.chainsMap f φ` is the map `inhomogeneousChains A ⟶ inhomogeneousChains B`
  induced by a group homomorphism `f : G →* H` and a representation morphism `φ : A ⟶ Res(f)(B)`.
* `groupHomology.map f φ n` is the map `Hₙ(G, A) ⟶ Hₙ(H, B)` induced by a group homomorphism
  `f : G →* H` and a representation morphism `φ : A ⟶ Res(f)(B)`.
* `groupHomology.coresNatTrans f n`: given a group homomorphism `f : G →* H`, this is a natural
  transformation of `n`th group homology functors which sends `A : Rep k H` to the "corestriction"
  map `Hₙ(G, Res(f)(A)) ⟶ Hₙ(H, A)` induced by `f` and the identity map on `Res(f)(A)`.
* `groupHomology.coinfNatTrans f n`: given a normal subgroup `S ≤ G`, this is a natural
  transformation of `n`th group homology functors which sends `A : Rep k G` to the "coinflation"
  map `Hₙ(G, A) ⟶ Hₙ(G ⧸ S, A_S)` induced by the quotient maps `G →* G ⧸ S` and `A →ₗ A_S`.
* `groupHomology.H1CoresCoinf A S` is the (exact) short complex
  `H₁(S, A) ⟶ H₁(G, A) ⟶ H₁(G ⧸ S, A_S)` for a normal subgroup `S ≤ G` and a `G`-representation
  `A`, defined using the corestriction and coinflation map in degree 1.

-/

universe v u

namespace groupHomology

open CategoryTheory Rep Finsupp Representation

variable {k G H : Type u} [CommRing k] [Group G] [Group H]
  {A : Rep k G} {B : Rep k H} (f : G →* H) (φ : A ⟶ res f B) (n : ℕ)

theorem congr {f₁ f₂ : G →* H} (h : f₁ = f₂) {φ : A ⟶ res f₁ B} {T : Type*}
    (F : (f : G →* H) → (φ : A ⟶ res f B) → T) :
    F f₁ φ = F f₂ (h ▸ φ) := by
  subst h
  rfl

set_option backward.isDefEq.respectTransparency false in
