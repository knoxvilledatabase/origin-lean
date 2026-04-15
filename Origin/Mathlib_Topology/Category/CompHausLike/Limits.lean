/-
Extracted from Topology/Category/CompHausLike/Limits.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Explicit limits and colimits

This file collects some constructions of explicit limits and colimits in `CompHausLike P`,
which may be useful due to their definitional properties.

## Main definitions

* `HasExplicitFiniteCoproducts`: A typeclass describing the property that forming all finite
  disjoint unions is stable under the property `P`.
  - Given this property, we deduce that `CompHausLike P` has finite coproducts and the inclusion
    functors to other `CompHausLike P'` and to `TopCat` preserve them.

* `HasExplicitPullbacks`: A typeclass describing the property that forming all "explicit pullbacks"
  is stable under the property `P`. Here, explicit pullbacks are defined as a subset of the product.
  - Given this property, we deduce that `CompHausLike P` has pullbacks and the inclusion
    functors to other `CompHausLike P'` and to `TopCat` preserve them.
  - We also define a variant `HasExplicitPullbacksOfInclusions` which is says that explicit
    pullbacks along inclusion maps into finite disjoint unions exist. `Stonean` has this property
    but not the stronger one.

## Main results

* Given `[HasExplicitPullbacksOfInclusions P]` (which is implied by `[HasExplicitPullbacks P]`),
  we provide an instance `FinitaryExtensive (CompHausLike P)`.
-/

open CategoryTheory Limits Topology

namespace CompHausLike

universe w u

section FiniteCoproducts

variable {P : TopCat.{max u w} → Prop} {α : Type w} [Finite α] (X : α → CompHausLike P)

abbrev HasExplicitFiniteCoproduct := HasProp P (Σ (a : α), X a)

variable [HasExplicitFiniteCoproduct X]

abbrev finiteCoproduct : CompHausLike P := CompHausLike.of P (Σ (a : α), X a)

def finiteCoproduct.ι (a : α) : X a ⟶ finiteCoproduct X :=
  ofHom _
  { toFun := fun x ↦ ⟨a, x⟩
    continuous_toFun := continuous_sigmaMk (σ := fun a ↦ X a) }

def finiteCoproduct.desc {B : CompHausLike P} (e : (a : α) → (X a ⟶ B)) :
    finiteCoproduct X ⟶ B :=
  ofHom _
  { toFun := fun ⟨a, x⟩ ↦ e a x
    continuous_toFun := by
      apply continuous_sigma
      intro a; exact (e a).hom.hom.continuous }
