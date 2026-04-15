/-
Extracted from RepresentationTheory/Homological/GroupCohomology/Functoriality.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Functoriality of group cohomology

Given a commutative ring `k`, a group homomorphism `f : G →* H`, a `k`-linear `H`-representation
`A`, a `k`-linear `G`-representation `B`, and a representation morphism `Res(f)(A) ⟶ B`, we get
a cochain map `inhomogeneousCochains A ⟶ inhomogeneousCochains B` and hence maps on
cohomology `Hⁿ(H, A) ⟶ Hⁿ(G, B)`.
We also provide extra API for these maps in degrees 0, 1, 2.

## Main definitions

* `groupCohomology.cochainsMap f φ` is the map `inhomogeneousCochains A ⟶ inhomogeneousCochains B`
  induced by a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`.
* `groupCohomology.map f φ n` is the map `Hⁿ(H, A) ⟶ Hⁿ(G, B)` induced by a group
  homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`.
* `groupCohomology.H1InfRes A S` is the short complex `H¹(G ⧸ S, A^S) ⟶ H¹(G, A) ⟶ H¹(S, A)` for
  a normal subgroup `S ≤ G` and a `G`-representation `A`.

-/

universe v u

namespace groupCohomology

open Rep CategoryTheory Representation

variable {k G H : Type u} [CommRing k] [Group G] [Group H]
  {A : Rep k H} {B : Rep k G} (f : G →* H) (φ : res f A ⟶ B) (n : ℕ)

theorem congr {f₁ f₂ : G →* H} (h : f₁ = f₂) {φ : res f₁ A ⟶ B} {T : Type*}
    (F : (f : G →* H) → (φ : res f A ⟶ B) → T) :
    F f₁ φ = F f₂ (h ▸ φ) := by
  subst h
  rfl

set_option backward.isDefEq.respectTransparency false in
