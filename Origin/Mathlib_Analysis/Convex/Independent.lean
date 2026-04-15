/-
Extracted from Analysis/Convex/Independent.lean
Genuine: 8 of 8 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Convex independence

This file defines convex independent families of points.

Convex independence is closely related to affine independence. In both cases, no point can be
written as a combination of others. When the combination is affine (that is, any coefficients), this
yields affine independence. When the combination is convex (that is, all coefficients are
nonnegative), then this yields convex independence. In particular, affine independence implies
convex independence.

## Main declarations

* `ConvexIndependent p`: Convex independence of the indexed family `p : ι → E`. Every point of the
  family only belongs to convex hulls of sets of the family containing it.
* `convexIndependent_iff_finset`: Carathéodory's theorem allows us to only check finsets to
  conclude convex independence.
* `Convex.convexIndependent_extremePoints`: Extreme points of a convex set are convex independent.

## References

* https://en.wikipedia.org/wiki/Convex_position

## TODO

Prove `AffineIndependent.convexIndependent`. This requires some glue between `affineCombination`
and `Finset.centerMass`.

## Tags

independence, convex position
-/

open Affine Finset Function

variable {𝕜 E ι : Type*}

section OrderedSemiring

variable (𝕜) [Semiring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]

def ConvexIndependent (p : ι → E) : Prop :=
  ∀ (s : Set ι) (x : ι), p x ∈ convexHull 𝕜 (p '' s) → x ∈ s

variable {𝕜}

theorem Subsingleton.convexIndependent [Subsingleton ι] (p : ι → E) : ConvexIndependent 𝕜 p := by
  intro s x hx
  have : (convexHull 𝕜 (p '' s)).Nonempty := ⟨p x, hx⟩
  rw [convexHull_nonempty_iff, Set.image_nonempty] at this
  rwa [Subsingleton.mem_iff_nonempty]

protected theorem ConvexIndependent.injective {p : ι → E} (hc : ConvexIndependent 𝕜 p) :
    Function.Injective p := by
  refine fun i j hij => hc {j} i ?_
  rw [hij, Set.image_singleton, convexHull_singleton]
  exact Set.mem_singleton _

theorem ConvexIndependent.comp_embedding {ι' : Type*} (f : ι' ↪ ι) {p : ι → E}
    (hc : ConvexIndependent 𝕜 p) : ConvexIndependent 𝕜 (p ∘ f) := by
  intro s x hx
  rw [← f.injective.mem_set_image]
  exact hc _ _ (by rwa [Set.image_image])

protected theorem ConvexIndependent.subtype {p : ι → E} (hc : ConvexIndependent 𝕜 p) (s : Set ι) :
    ConvexIndependent 𝕜 fun i : s => p i :=
  hc.comp_embedding (Embedding.subtype _)

protected theorem ConvexIndependent.range {p : ι → E} (hc : ConvexIndependent 𝕜 p) :
    ConvexIndependent 𝕜 ((↑) : Set.range p → E) := by
  let f : Set.range p → ι := fun x => x.property.choose
  have hf : ∀ x, p (f x) = x := fun x => x.property.choose_spec
  let fe : Set.range p ↪ ι := ⟨f, fun x₁ x₂ he => Subtype.ext (hf x₁ ▸ hf x₂ ▸ he ▸ rfl)⟩
  convert hc.comp_embedding fe
  ext
  rw [Embedding.coeFn_mk, comp_apply, hf]

protected theorem ConvexIndependent.mono {s t : Set E} (hc : ConvexIndependent 𝕜 ((↑) : t → E))
    (hs : s ⊆ t) : ConvexIndependent 𝕜 ((↑) : s → E) :=
  hc.comp_embedding (s.embeddingOfSubset t hs)

theorem Function.Injective.convexIndependent_iff_set {p : ι → E} (hi : Function.Injective p) :
    ConvexIndependent 𝕜 ((↑) : Set.range p → E) ↔ ConvexIndependent 𝕜 p :=
  ⟨fun hc =>
    hc.comp_embedding
      (⟨fun i => ⟨p i, Set.mem_range_self _⟩, fun _ _ h => hi (Subtype.mk_eq_mk.1 h)⟩ :
        ι ↪ Set.range p),
    ConvexIndependent.range⟩
