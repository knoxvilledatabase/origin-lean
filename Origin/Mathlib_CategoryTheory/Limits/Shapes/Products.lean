/-
Extracted from CategoryTheory/Limits/Shapes/Products.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Categorical (co)products

This file defines (co)products as special cases of (co)limits.

A product is the categorical generalization of the object `Π i, f i` where `f : ι → C`. It is a
limit cone over the diagram formed by `f`, implemented by converting `f` into a functor
`Discrete ι ⥤ C`.

A coproduct is the dual concept.

## Main definitions

* a `Fan` is a cone over a discrete category
* `Fan.mk` constructs a fan from an indexed collection of maps
* a `Pi` is a `limit (Discrete.functor f)`

Each of these has a dual.

## Implementation notes
As with the other special shapes in the limits library, all the definitions here are given as
`abbrev`s of the general statements for limits, so all the `simp` lemmas and theorems about
general limits can be used.
-/

noncomputable section

universe w w' w₂ w₃ v v₂ u u₂

open CategoryTheory

namespace CategoryTheory.Limits

variable {β : Type w} {α : Type w₂} {γ : Type w₃}

variable {C : Type u} [Category.{v} C]

abbrev Fan (f : β → C) :=
  Cone (Discrete.functor f)

abbrev Cofan (f : β → C) :=
  Cocone (Discrete.functor f)
