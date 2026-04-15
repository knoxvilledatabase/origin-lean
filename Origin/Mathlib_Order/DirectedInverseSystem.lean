/-
Extracted from Order/DirectedInverseSystem.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Definition of direct systems, inverse systems, and cardinalities in specific inverse systems

The first part of this file concerns directed systems: `DirectLimit` is defined as the quotient
of the disjoint union (`Sigma` type) by an equivalence relation (`Setoid`): compare
`CategoryTheory.Limits.Types.Quot`, which is a quotient by a plain relation.
Recursion and induction principles for constructing functions from and to `DirectLimit` and
proving things about elements in `DirectLimit`.

In the second part we compute the cardinality of each node in an inverse system `F i` indexed by a
well-order in which every map between successive nodes has constant fiber `X i`, and every limit
node is the `limit` of the inverse subsystem formed by all previous nodes.
(To avoid importing `Cardinal`, we in fact construct a bijection rather than
stating the result in terms of `Cardinal.mk`.)

The most tricky part of the whole argument happens at limit nodes: if `i : ι` is a limit,
what we have in hand is a family of bijections `F j ≃ ∀ l : Iio j, X l` for every `j < i`,
which we would like to "glue" up to a bijection `F i ≃ ∀ l : Iio i, X l`. We denote
`∀ l : Iio i, X l` by `PiLT X i`, and they form an inverse system just like the `F i`.
Observe that at a limit node `i`, `PiLT X i` is actually the inverse limit of `PiLT X j` over
all `j < i` (`piLTLim`). If the family of bijections `F j ≃ PiLT X j` is natural (`IsNatEquiv`),
we immediately obtain a bijection between the limits `limit F i ≃ PiLT X i` (`invLimEquiv`),
and we just need an additional bijection `F i ≃ limit F i` to obtain the desired
extension `F i ≃ PiLT X i` to the limit node `i`. (We do have such a bijection, for example, when
we consider a directed system of algebraic structures (say fields) `K i`, and `F` is
the inverse system of homomorphisms `K i ⟶ K` into a specific field `K`.)

Now our task reduces to the recursive construction of a *natural* family of bijections for each `i`.
We can prove that a natural family over all `l ≤ i` (`Iic i`) extends to a natural family over
`Iic i⁺` (where `i⁺ = succ i`), but at a limit node, recursion stops working: we have natural
families over all `Iic j` for each `j < i`, but we need to know that they glue together to form a
natural family over all `l < i` (`Iio i`). This intricacy did not occur to the author when he
thought he had a proof and set out to formalize it. Fortunately he was able to figure out an
additional `compat` condition (compatibility with the bijections `F i⁺ ≃ F i × X i` in the `X`
component) that guarantees uniqueness (`unique_pEquivOn`) and hence gluability (well-definedness):
see `pEquivOnGlue`. Instead of just a family of natural families, we actually construct a family of
the stronger `PEquivOn`s that bundles the `compat` condition, in order for the inductive argument
to work.

It is possible to circumvent the introduction of the `compat` condition using Zorn's lemma;
if there is a chain of natural families (i.e. for any two families in the chain, one is an
extension of the other) over lower sets (which are all of the form `Iic`, `Iio`, or `univ`),
we can clearly take the union to get a natural family that extends them all. If a maximal
natural family has domain `Iic i` or `Iio i` (`i` a limit), we already know how to extend it
one step further to `Iic i⁺` or `Iic i` respectively, so it must be the case that the domain
is everything. However, the author chose the `compat` approach in the end because it constructs
the distinguished bijection that is compatible with the projections to all `X i`.

-/

open Order Set

variable {ι : Type*} [Preorder ι] {F₁ F₂ F X : ι → Type*}

variable (F) in

class DirectedSystem (f : ∀ ⦃i j⦄, i ≤ j → F i → F j) : Prop where
  map_self ⦃i⦄ (x : F i) : f le_rfl x = x
  map_map ⦃k j i⦄ (hij : i ≤ j) (hjk : j ≤ k) (x : F i) : f hjk (f hij x) = f (hij.trans hjk) x

section DirectedSystem

variable {T₁ : ∀ ⦃i j : ι⦄, i ≤ j → Sort*} (f₁ : ∀ i j (h : i ≤ j), T₁ h)

variable [∀ ⦃i j⦄ (h : i ≤ j), FunLike (T₁ h) (F₁ i) (F₁ j)] [DirectedSystem F₁ (f₁ · · ·)]

variable {T₂ : ∀ ⦃i j : ι⦄, i ≤ j → Sort*} (f₂ : ∀ i j (h : i ≤ j), T₂ h)

variable [∀ ⦃i j⦄ (h : i ≤ j), FunLike (T₂ h) (F₂ i) (F₂ j)] [DirectedSystem F₂ (f₂ · · ·)]

variable {T : ∀ ⦃i j : ι⦄, i ≤ j → Sort*} (f : ∀ i j (h : i ≤ j), T h)

variable [∀ ⦃i j⦄ (h : i ≤ j), FunLike (T h) (F i) (F j)] [DirectedSystem F (f · · ·)]

theorem DirectedSystem.map_self' ⦃i⦄ (x) : f i i le_rfl x = x :=
  DirectedSystem.map_self (f := (f · · ·)) x

theorem DirectedSystem.map_map' ⦃i j k⦄ (hij hjk x) :
    f j k hjk (f i j hij x) = f i k (hij.trans hjk) x :=
  DirectedSystem.map_map (f := (f · · ·)) hij hjk x

namespace DirectLimit

open DirectedSystem

variable [IsDirectedOrder ι]
