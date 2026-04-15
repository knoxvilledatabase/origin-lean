/-
Extracted from CategoryTheory/Limits/Indization/IndObject.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Ind-objects

For a presheaf `A : Cᵒᵖ ⥤ Type v` we define the type `IndObjectPresentation A` of presentations
of `A` as a small filtered colimit of representable presheaves and define the predicate
`IsIndObject A` asserting that there is at least one such presentation.

A presheaf is an ind-object if and only if the category `CostructuredArrow yoneda A` is filtered
and finally small. In this way, `CostructuredArrow yoneda A` can be thought of the universal
indexing category for the representation of `A` as a small filtered colimit of representable
presheaves.

## Future work

There are various useful ways to understand natural transformations between ind-objects in terms
of their presentations.

The ind-objects form a locally `v`-small category `IndCategory C` which has numerous interesting
properties.

## Implementation notes

One might be tempted to introduce another universe parameter and consider being a `w`-ind-object
as a property of presheaves `C ⥤ Type max v w`. This comes with significant technical hurdles.
The recommended alternative is to consider ind-objects over `ULiftHom.{w} C` instead.

## References
* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], Chapter 6
-/

universe v v' u u'

namespace CategoryTheory.Limits

section NonSmall

variable {C : Type u} [Category.{v} C]

structure IndObjectPresentation (A : Cᵒᵖ ⥤ Type v) where
  /-- The indexing category of the filtered colimit presentation -/
  I : Type v
  /-- The indexing category of the filtered colimit presentation -/
  [ℐ : SmallCategory I]
  [hI : IsFiltered I]
  /-- The diagram of the filtered colimit presentation -/
  F : I ⥤ C
  /-- Use `IndObjectPresentation.cocone` instead. -/
  ι : F ⋙ yoneda ⟶ (Functor.const I).obj A
  /-- Use `IndObjectPresentation.coconeIsColimit` instead. -/
  isColimit : IsColimit (Cocone.mk A ι)

namespace IndObjectPresentation
