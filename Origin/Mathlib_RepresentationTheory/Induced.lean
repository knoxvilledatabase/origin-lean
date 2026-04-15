/-
Extracted from RepresentationTheory/Induced.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Induced representations

Given a commutative ring `k`, a group homomorphism `φ : G →* H`, and a `k`-linear
`G`-representation `A`, this file introduces the induced representation $Ind_G^H(A)$ of `A` as
an `H`-representation.

By `ind φ A` we mean the `(k[H] ⊗[k] A)_G` with the `G`-representation on `k[H]` defined by `φ`.
We define a representation of `H` on this submodule by sending `h : H` and `⟦h₁ ⊗ₜ a⟧` to
`⟦h₁h⁻¹ ⊗ₜ a⟧`.

We also prove that the restriction functor `Rep k H ⥤ Rep k G` along `φ` is right adjoint to the
induction functor and hence that the induction functor preserves colimits.

Additionally, we show that the functor `Rep k H ⥤ ModuleCat k` sending `B : Rep k H` to
`(Ind(φ)(A) ⊗ B))_H` is naturally isomorphic to the one sending `B` to `(A ⊗ Res(φ)(B))_G`. This
is used to prove Shapiro's lemma in
`Mathlib/RepresentationTheory/Homological/GroupHomology/Shapiro.lean`.

## Main definitions

* `Representation.ind φ ρ` : given a group homomorphism `φ : G →* H`, this is the induction of a
  `G`-representation `(A, ρ)` along `φ`, defined as `(k[H] ⊗[k] A)_G` and with `H`-action given by
  `h • ⟦h₁ ⊗ₜ a⟧ := ⟦h₁h⁻¹ ⊗ₜ a⟧` for `h, h₁ : H`, `a : A`.
* `Rep.indResAdjunction k φ`: given a group homomorphism `φ : G →* H`, this is the adjunction
  between the induction functor along `φ` and the restriction functor `Rep k H ⥤ Rep k G`
  along `φ`.
* `Rep.coinvariantsTensorIndNatIso φ A` : given a group homomorphism `φ : G →* H` and
  `A : Rep k G`, this is a natural isomorphism between the functor sending `B : Rep k H` to
  `(Ind(φ)(A) ⊗ B))_H` and the one sending `B` to `(A ⊗ Res(φ)(B))_G`. Used to prove Shapiro's
  lemma.

-/

universe t w w' u u' v v'

namespace Representation

open Finsupp TensorProduct

variable {k G H : Type*} [CommRing k] [Group G] [Group H] (φ : G →* H) {A B : Type*}
  [AddCommGroup A] [Module k A] (ρ : Representation k G A)
  [AddCommGroup B] [Module k B] (τ : Representation k G B)

abbrev IndV := Coinvariants (V := TensorProduct k (H →₀ k) A)
  (Representation.tprod ((leftRegular k H).comp φ) ρ)

noncomputable abbrev IndV.mk (h : H) : A →ₗ[k] IndV φ ρ :=
  Coinvariants.mk _ ∘ₗ TensorProduct.mk k _ _ (single h 1)
