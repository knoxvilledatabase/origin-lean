/-
Extracted from Algebra/Homology/DerivedCategory/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # The derived category of an abelian category

In this file, we construct the derived category `DerivedCategory C` of an
abelian category `C`. It is equipped with a triangulated structure.

The derived category is defined here as the localization of cochain complexes
indexed by `ℤ` with respect to quasi-isomorphisms: it is a type synonym of
`HomologicalComplexUpToQuasiIso C (ComplexShape.up ℤ)`. Then, we have a
localization functor `DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C`.
It was already shown in the file `Mathlib/Algebra/Homology/Localization.lean` that the induced
functor `DerivedCategory.Qh : HomotopyCategory C (ComplexShape.up ℤ) ⥤ DerivedCategory C`
is a localization functor with respect to the class of morphisms
`HomotopyCategory.quasiIso C (ComplexShape.up ℤ)`. In the file
`HomotopyCategory.Acyclic`, it was shown that this class of quasiisomorphisms
consists of morphisms whose cone belongs to the triangulated subcategory
`HomotopyCategory.subcategoryAcyclic C` of acyclic complexes. Then, the triangulated
structure on `DerivedCategory C` is deduced from the triangulated structure
on the homotopy category (see file `Mathlib/Algebra/Homology/HomotopyCategory/Triangulated.lean`)
using the localization theorem for triangulated categories which was obtained
in the file `Mathlib/CategoryTheory/Localization/Triangulated.lean`.

## Implementation notes

If `C : Type u` and `Category.{v} C`, the constructed localized category of cochain
complexes with respect to quasi-isomorphisms has morphisms in `Type (max u v)`.
However, in certain circumstances, it shall be possible to prove that they are `v`-small
(when `C` is a Grothendieck abelian category (e.g. the category of modules over a ring),
it should be so by a theorem of Hovey).

Then, when working with derived categories in mathlib, the user should add the variable
`[HasDerivedCategory.{w} C]` which is the assumption that there is a chosen derived
category with morphisms in `Type w`. When derived categories are used in order to
prove statements which do not involve derived categories, the `HasDerivedCategory.{max u v}`
instance should be obtained at the beginning of the proof, using the term
`HasDerivedCategory.standard C`.

## TODO (@joelriou)

- construct the distinguished triangle associated to a short exact sequence
  of cochain complexes (done), and compare the associated connecting homomorphism
  with the one defined in `Algebra.Homology.HomologySequence`.

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*][verdier1996]
* [Mark Hovey, *Model category structures on chain complexes of sheaves*][hovey-2001]

-/

assert_not_exists TwoSidedIdeal

universe w v u

open CategoryTheory Limits Pretriangulated

variable (C : Type u) [Category.{v} C] [Abelian C]

abbrev HasDerivedCategory := MorphismProperty.HasLocalization.{w}
  (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
