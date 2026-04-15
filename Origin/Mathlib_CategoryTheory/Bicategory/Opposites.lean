/-
Extracted from CategoryTheory/Bicategory/Opposites.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Opposite bicategories

We construct the 1-cell opposite of a bicategory `B`, called `Bᵒᵖ`. It is defined as follows
* The objects of `Bᵒᵖ` correspond to objects of `B`.
* The morphisms `X ⟶ Y` in `Bᵒᵖ` are the morphisms `Y ⟶ X` in `B`.
* The 2-morphisms `f ⟶ g` in `Bᵒᵖ` are the 2-morphisms `f ⟶ g` in `B`. In other words, the
  directions of the 2-morphisms are preserved.

## Remarks
There are multiple notions of opposite categories for bicategories.
- There is 1-cell dual `Bᵒᵖ` as defined above.
- There is the 2-cell dual, `Cᶜᵒ` where only the 2-morphisms are reversed
- There is the bi-dual `Cᶜᵒᵒᵖ` where the directions of both the 1-morphisms and the 2-morphisms
  are reversed.

## TODO

* Define the 2-cell dual `Cᶜᵒ`.
* Provide various lemmas for going between `LocallyDiscrete Cᵒᵖ` and `(LocallyDiscrete C)ᵒᵖ`.

Note: `Cᶜᵒᵒᵖ` is WIP by Christian Merten.

-/

universe w v u

open CategoryTheory Bicategory Opposite

namespace Bicategory.Opposite

variable {B : Type u} [Bicategory.{w, v} B]

structure Hom2 {a b : Bᵒᵖ} (f g : a ⟶ b) where
  op2' ::
  /-- `Bᵒᵖ` preserves the direction of all 2-morphisms in `B` -/
  unop2 : f.unop ⟶ g.unop

open Hom2
