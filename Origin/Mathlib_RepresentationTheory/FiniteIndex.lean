/-
Extracted from RepresentationTheory/FiniteIndex.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# (Co)induced representations of a finite index subgroup

Given a commutative ring `k`, a finite index subgroup `S ≤ G`, and a `k`-linear `S`-representation
`A`, this file defines an isomorphism $Ind_S^G(A) ≅ Coind_S^G(A)$. Given `g : G` and `a : A`, the
forward map sends `⟦g ⊗ₜ[k] a⟧` to the function `G → A` supported at `sg` by `ρ(s)(a)` for `s : S`
and which is 0 elsewhere. Meanwhile, the inverse sends `f : G → A` to `∑ᵢ ⟦gᵢ ⊗ₜ[k] f(gᵢ)⟧` for
`1 ≤ i ≤ n`, where `g₁, ..., gₙ` is a set of right coset representatives of `S`.

## Main definitions

* `Rep.indCoindIso A`: An isomorphism `Ind_S^G(A) ≅ Coind_S^G(A)` for a finite index subgroup
  `S ≤ G` and a `k`-linear `S`-representation `A`.
* `Rep.indCoindNatIso k S`: A natural isomorphism between the functors `Ind_S^G` and `Coind_S^G`.

TODO : Fix the universe constraint
-/

universe t w u u' v v'

namespace Rep

open CategoryTheory Finsupp TensorProduct Representation

variable {k : Type u} {G : Type v} [CommRing k] [Group G] {S : Subgroup G}
  [DecidableRel (QuotientGroup.rightRel S)] (A : Rep.{w} k S)

noncomputable def indToCoindAux (g : G) : A →ₗ[k] (G → A) :=
  LinearMap.pi (fun g₁ => if h : (QuotientGroup.rightRel S).r g₁ g then
    A.ρ ⟨g₁ * g⁻¹, by rcases h with ⟨s, rfl⟩; exact mul_inv_cancel_right s.1 g ▸ s.2⟩ else 0)

variable {A}
