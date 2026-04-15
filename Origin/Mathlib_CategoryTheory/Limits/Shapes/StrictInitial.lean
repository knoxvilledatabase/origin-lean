/-
Extracted from CategoryTheory/Limits/Shapes/StrictInitial.lean
Genuine: 5 of 6 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Strict initial objects

This file sets up the basic theory of strict initial objects: initial objects where every morphism
to it is an isomorphism. This generalises a property of the empty set in the category of sets:
namely that the only function to the empty set is from itself.

We say `C` has strict initial objects if every initial object is strict, i.e. given any morphism
`f : A ⟶ I` where `I` is initial, then `f` is an isomorphism.
Strictly speaking, this says that *any* initial object must be strict, rather than that strict
initial objects exist, which turns out to be a more useful notion to formalise.

If the binary product of `X` with a strict initial object exists, it is also initial.

To show a category `C` with an initial object has strict initial objects, the most convenient way
is to show any morphism to the (chosen) initial object is an isomorphism and use
`hasStrictInitialObjects_of_initial_is_strict`.

The dual notion (strict terminal objects) occurs much less frequently in practice so is ignored.

## TODO

* Construct examples of this: `Type*`, `TopCat`, `Groupoid`, simplicial types, posets.
* Construct the bottom element of the subobject lattice given strict initials.
* Show Cartesian closed categories have strict initials

## References
* https://ncatlab.org/nlab/show/strict+initial+object
-/

universe v u

namespace CategoryTheory

namespace Limits

open Category

variable (C : Type u) [Category.{v} C]

section StrictInitial

class HasStrictInitialObjects : Prop where
  out : ∀ {I A : C} (f : A ⟶ I), IsInitial I → IsIso f

variable {C}

variable [HasStrictInitialObjects C] {I : C}

theorem IsInitial.isIso_to (hI : IsInitial I) {A : C} (f : A ⟶ I) : IsIso f :=
  HasStrictInitialObjects.out f hI

theorem IsInitial.strict_hom_ext (hI : IsInitial I) {A : C} (f g : A ⟶ I) : f = g := by
  haveI := hI.isIso_to f
  haveI := hI.isIso_to g
  exact eq_of_inv_eq_inv (hI.hom_ext (inv f) (inv g))

theorem IsInitial.subsingleton_to (hI : IsInitial I) {A : C} : Subsingleton (A ⟶ I) :=
  ⟨hI.strict_hom_ext⟩

noncomputable

def IsInitial.ofStrict {X Y : C} (f : X ⟶ Y)
    (hY : IsInitial Y) : IsInitial X :=
  letI := hY.isIso_to f
  hY.ofIso (asIso f).symm

-- INSTANCE (free from Core): (priority
