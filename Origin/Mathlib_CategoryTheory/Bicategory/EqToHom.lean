/-
Extracted from CategoryTheory/Bicategory/EqToHom.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# `eqToHom` in bicategories

This file records some of the behavior of `eqToHom` 1-morphisms and
2-morphisms in bicategories.

Given an equality of objects `h : x = y` in a bicategory, there is a 1-morphism
`eqToHom h : x ⟶ y` just like in an ordinary category. The definitional property
of this morphism is that if `h : x = x`, `eqToHom h = 𝟙 x`. This is
implemented as the `eqToHom` morphism in the `CategoryStruct` underlying the
bicategory.

Unlike the situation in ordinary category theory, these 1-morphisms do not
compose strictly: `eqToHom h.trans h'` is merely isomorphic to
`eqToHom h ≫ eqToHom h'`. We define this isomorphism as
`CategoryTheory.Bicategory.eqToHomTransIso`.

Given an equality of 1-morphisms, we show that various bicategorical
structure morphisms such as unitors, associators and whiskering conjugate
well under `eqToHom`s.

## TODO
* Define `eqToEquiv` that puts the `eqToHom`s in an `Equivalence` between
  objects.
-/

universe w v u

namespace CategoryTheory.Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

def eqToHomTransIso {x y z : B} (e₁ : x = y) (e₂ : y = z) :
    eqToHom (e₁.trans e₂) ≅ eqToHom e₁ ≫ eqToHom e₂ :=
  e₂ ▸ e₁ ▸ (λ_ (𝟙 x)).symm
