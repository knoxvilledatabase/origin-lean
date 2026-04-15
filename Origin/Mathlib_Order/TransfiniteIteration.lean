/-
Extracted from Order/TransfiniteIteration.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Transfinite iteration of a function `I → I`

Given `φ : I → I` where `[SupSet I]`, we define the `j`th transfinite iteration of `φ`
for any `j : J`, with `J` a well-ordered type: this is `transfiniteIterate φ j : I → I`.
If `i₀ : I`, then `transfiniteIterate φ ⊥ i₀ = i₀`; if `j` is a non-maximal element,
then `transfiniteIterate φ (Order.succ j) i₀ = φ (transfiniteIterate φ j i₀)`; and
if `j` is a limit element, `transfiniteIterate φ j i₀` is the supremum
of the `transfiniteIterate φ l i₀` for `l < j`.

If `I` is a complete lattice, we show that `j ↦ transfiniteIterate φ j i₀` is
a monotone function if `i ≤ φ i` for all `i`. Moreover, if `i < φ i`
when `i ≠ ⊤`, we show in the lemma `top_mem_range_transfiniteIteration` that
there exists `j : J` such that `transfiniteIteration φ i₀ j = ⊤` if we assume that
`j ↦ transfiniteIterate φ i₀ j : J → I` is not injective (which shall hold
when we know `Cardinal.mk I < Cardinal.mk J`).

## TODO (@joelriou)
* deduce that in a Grothendieck abelian category, there is a *set* `I` of monomorphisms
  such that any monomorphism is a transfinite composition of pushouts of morphisms in `I`,
  and then an object `X` is injective iff `X ⟶ 0` has the right lifting
  property with respect to `I`.

-/

universe w u

variable {I : Type u} [SupSet I] (φ : I → I)
  {J : Type w} [LinearOrder J] [SuccOrder J] [WellFoundedLT J]

noncomputable def transfiniteIterate (j : J) : I → I :=
  SuccOrder.limitRecOn j
    (fun _ _ ↦ id) (fun _ _ g ↦ φ ∘ g) (fun y _ h ↦ ⨆ (x : Set.Iio y), h x.1 x.2)
