/-
Extracted from CategoryTheory/Subobject/Classifier/Defs.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Subobject Classifier

We define a structure containing the data of a subobject classifier in a category `C` as
`CategoryTheory.Subobject.Classifier C`.

c.f. the following Lean 3 code, where similar work was done:
https://github.com/b-mehta/topos/blob/master/src/subobject_classifier.lean

## Main definitions

Let `C` refer to a category with a terminal object.

* `CategoryTheory.Subobject.Classifier C` is the data of a subobject classifier in `C`.

* `CategoryTheory.HasSubobjectClassifier C` says that there is at least one subobject classifier.
  `Ω C` denotes a choice of subobject classifier.

## Main results

* It is a theorem that the truth morphism `⊤_ C ⟶ Ω C` is a (split, and therefore regular)
  monomorphism, simply because its source is the terminal object.

* An instance of `IsRegularMonoCategory C` is exhibited for any category with a subobject
  classifier.

* `CategoryTheory.Subobject.Classifier.representableBy`: any subobject classifier `Ω` in `C`
  represents the subobjects functor `CategoryTheory.Subobject.presheaf C`, assuming `C` has
  pullbacks.

* `CategoryTheory.SubobjectRepresentableBy.classifier`: any representation `Ω` of
  `CategoryTheory.Subobject.presheaf C` is a subobject classifier in `C`.

* `CategoryTheory.hasClassifier_isRepresentable_iff`: from the two above mappings, we get that a
  category `C` with pullbacks has a subobject classifier if and only if the subobjects presheaf
  `CategoryTheory.Subobject.presheaf C` is representable (Proposition 1 in Section I.3 of [MM92]).

## References

* [S. MacLane and I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]

-/

universe v v₀ u u₀

namespace CategoryTheory

open Category Limits Functor IsPullback

variable {C : Type u} [Category.{v} C]

namespace Subobject

structure Classifier (C : Type u) [Category.{v} C] where
  /-- The domain of the truth morphism -/
  Ω₀ : C
  /-- The codomain of the truth morphism -/
  Ω : C
  /-- The truth morphism of the subobject classifier -/
  truth : Ω₀ ⟶ Ω
  /-- The truth morphism is a monomorphism -/
  mono_truth : Mono truth := by infer_instance
  /-- The top arrow in the pullback square -/
  χ₀ (U : C) : U ⟶ Ω₀
  /-- For any monomorphism `U ⟶ X`, there is an associated characteristic map `X ⟶ Ω`. -/
  χ {U X : C} (m : U ⟶ X) [Mono m] : X ⟶ Ω
  /-- `χ₀ U` and `χ m` form the appropriate pullback square. -/
  isPullback {U X : C} (m : U ⟶ X) [Mono m] : IsPullback m (χ₀ U) (χ m) truth
  /-- `χ m` is the only map `X ⟶ Ω` which forms the appropriate pullback square for any `χ₀'`. -/
  uniq {U X : C} (m : U ⟶ X) [Mono m] {χ₀' : U ⟶ Ω₀} {χ' : X ⟶ Ω}
    (hχ' : IsPullback m χ₀' χ' truth) : χ' = χ m
