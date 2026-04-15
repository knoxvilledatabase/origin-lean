/-
Extracted from CategoryTheory/Adjunction/Quadruple.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Adjoint quadruples

This file concerns adjoint quadruples `L ⊣ F ⊣ G ⊣ R` of functors `L G : C ⥤ D`, `F R : D ⥤ C`.
We bundle the adjunctions in a structure `Quadruple L F G R` and make the two triples `Triple L F G`
and `Triple F G R` accessible as `Quadruple.leftTriple` and `Quadruple.rightTriple`.

Currently the only two results are the following:
* When `F` and `R` are fully faithful, the components of the induced natural transformation `G ⟶ L`
  are epimorphisms iff the components of the natural transformation `F ⟶ R` are monomorphisms.
* When `L` and `G` are fully faithful, the components of the induced natural transformation `L ⟶ G`
  are epimorphisms iff the components of the natural transformation `R ⟶ F` are monomorphisms.

This is in particular relevant for the adjoint quadruples `π₀ ⊣ disc ⊣ Γ ⊣ codisc` that appear in
cohesive topoi, and can be found e.g. as proposition 2.7
[here](https://ncatlab.org/nlab/show/cohesive+topos).

Note that by `Triple.fullyFaithfulEquiv`, in an adjoint quadruple `L ⊣ F ⊣ G ⊣ R` `L` is fully
faithful iff `G` is and `F` is fully faithful iff `R` is; these lemmas thus cover all cases in which
some of the functors are fully faithful. We opt to include only those typeclass assumptions that are
needed for the theorem statements, so some lemmas require only e.g. `F` to be fully faithful when
really this means `F` and `R` both must be.
-/

open CategoryTheory Limits Functor Adjunction Triple

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

variable (L : C ⥤ D) (F : D ⥤ C) (G : C ⥤ D) (R : D ⥤ C)

structure CategoryTheory.Adjunction.Quadruple where
  /-- Adjunction `L ⊣ F` of the adjoint quadruple `L ⊣ F ⊣ G ⊣ R`. -/
  adj₁ : L ⊣ F
  /-- Adjunction `F ⊣ G` of the adjoint quadruple `L ⊣ F ⊣ G ⊣ R`. -/
  adj₂ : F ⊣ G
  /-- Adjunction `G ⊣ R` of the adjoint quadruple `L ⊣ F ⊣ G ⊣ R`. -/
  adj₃ : G ⊣ R

namespace CategoryTheory.Adjunction.Quadruple

variable {L F G R} (q : Quadruple L F G R)
