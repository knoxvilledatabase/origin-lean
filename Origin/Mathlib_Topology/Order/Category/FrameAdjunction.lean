/-
Extracted from Topology/Order/Category/FrameAdjunction.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Adjunction between Locales and Topological Spaces

This file defines the point functor from the category of locales to topological spaces
and proves that it is right adjoint to the forgetful functor from topological spaces to locales.

## Main declarations

* `Locale.pt`: the *points* functor from the category of locales to the category of topological
  spaces.

* `Locale.adjunctionTopToLocalePT`: the adjunction between the functors `topToLocale` and `pt`.

## Motivation

This adjunction provides a framework in which several Stone-type dualities fit.

## Implementation notes

* In naming the various functions below, we follow common terminology and reserve the word *point*
  for an inhabitant of a type `X` which is a topological space, while we use the word *element* for
  an inhabitant of a type `L` which is a locale.

## References

* [J. Picado and A. Pultr, Frames and Locales: topology without points][picado2011frames]

## Tags

topological space, frame, locale, Stone duality, adjunction, points
-/

open CategoryTheory Order Set Topology TopologicalSpace

namespace Locale

/-! ### Definition of the points functor `pt` -/

section pt_definition

variable (L : Type*) [CompleteLattice L]

abbrev PT := FrameHom L Prop
