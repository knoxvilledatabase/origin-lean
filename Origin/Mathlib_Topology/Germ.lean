/-
Extracted from Topology/Germ.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Germs of functions between topological spaces

In this file, we prove basic properties of germs of functions between topological spaces,
with respect to the neighbourhood filter `𝓝 x`.

## Main definitions and results

* `Filter.Germ.value φ f`: value associated to the germ `φ` at a point `x`, w.r.t. the
  neighbourhood filter at `x`. This is the common value of all representatives of `φ` at `x`.
* `Filter.Germ.valueOrderRingHom` and friends: the map `Germ (𝓝 x) E → E` is a
  monoid homomorphism, 𝕜-linear map, ring homomorphism, monotone ring homomorphism

* `RestrictGermPredicate`: given a predicate on germs `P : Π x : X, germ (𝓝 x) Y → Prop` and
  `A : set X`, build a new predicate on germs `restrictGermPredicate P A` such that
  `(∀ x, RestrictGermPredicate P A x f) ↔ ∀ᶠ x near A, P x f`;
  `forall_restrictGermPredicate_iff` is this equivalence.

* `Filter.Germ.sliceLeft, sliceRight`: map the germ of functions `X × Y → Z` at `p = (x,y) ∈ X × Y`
  to the corresponding germ of functions `X → Z` at `x ∈ X` resp. `Y → Z` at `y ∈ Y`.
* `eq_of_germ_isConstant`: if each germ of `f : X → Y` is constant and `X` is pre-connected,
  `f` is constant.
-/

open scoped Topology

open Filter Set

variable {X Y Z : Type*} [TopologicalSpace X] {f g : X → Y} {A : Set X} {x : X}

namespace Filter.Germ

def value {X α : Type*} [TopologicalSpace X] {x : X} (φ : Germ (𝓝 x) α) : α :=
  Quotient.liftOn' φ (fun f ↦ f x) fun f g h ↦ by dsimp only; rw [Eventually.self_of_nhds h]

theorem value_smul {α β : Type*} [SMul α β] (φ : Germ (𝓝 x) α)
    (ψ : Germ (𝓝 x) β) : (φ • ψ).value = φ.value • ψ.value :=
  Germ.inductionOn φ fun _ ↦ Germ.inductionOn ψ fun _ ↦ rfl
