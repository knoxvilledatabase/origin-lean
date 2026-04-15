/-
Extracted from AlgebraicTopology/SimplicialCategory/Basic.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Simplicial categories

A simplicial category is a category `C` that is enriched over the
category of simplicial sets in such a way that morphisms in
`C` identify to the `0`-simplices of the enriched hom.

## TODO

* construct a simplicial category structure on simplicial objects, so
  that it applies in particular to simplicial sets
* obtain the adjunction property `(K ⊗ X ⟶ Y) ≃ (K ⟶ sHom X Y)` when `K`, `X`, and `Y`
  are simplicial sets
* develop the notion of "simplicial tensor" `K ⊗ₛ X : C` with `K : SSet` and `X : C`
  an object in a simplicial category `C`
* define the notion of path between `0`-simplices of simplicial sets
* deduce the notion of homotopy between morphisms in a simplicial category
* obtain that homotopies in simplicial categories can be interpreted as given
  by morphisms `Δ[1] ⊗ X ⟶ Y`.

## References
* [Daniel G. Quillen, *Homotopical algebra*, II §1][quillen-1967]

-/

universe v u

open CategoryTheory Category Simplicial MonoidalCategory

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

abbrev SimplicialCategory := EnrichedOrdinaryCategory SSet.{v} C

namespace SimplicialCategory

variable [SimplicialCategory C]

variable {C}

abbrev sHom (K L : C) : SSet.{v} := K ⟶[SSet] L

abbrev sHomComp (K L M : C) : sHom K L ⊗ sHom L M ⟶ sHom K M := eComp SSet K L M

def homEquiv' (K L : C) : (K ⟶ L) ≃ sHom K L _⦋0⦌ :=
  (eHomEquiv SSet).trans (sHom K L).unitHomEquiv

variable (C) in

noncomputable abbrev sHomFunctor : Cᵒᵖ ⥤ C ⥤ SSet.{v} := eHomFunctor _ _

end SimplicialCategory

end CategoryTheory
