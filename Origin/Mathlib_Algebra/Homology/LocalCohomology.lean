/-
Extracted from Algebra/Homology/LocalCohomology.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Local cohomology.

This file defines the `i`-th local cohomology module of an `R`-module `M` with support in an
ideal `I` of `R`, where `R` is a commutative ring, as the direct limit of Ext modules:

Given a collection of ideals cofinal with the powers of `I`, consider the directed system of
quotients of `R` by these ideals, and take the direct limit of the system induced on the `i`-th
Ext into `M`.  One can, of course, take the collection to simply be the integral powers of `I`.

## References

* [M. Hochster, *Local cohomology*][hochsterunpublished]
  <https://dept.math.lsa.umich.edu/~hochster/615W22/lcc.pdf>
* [R. Hartshorne, *Local cohomology: A seminar given by A. Grothendieck*][hartshorne61]
* [M. Brodmann and R. Sharp, *Local cohomology: An algebraic introduction with geometric
  applications*][brodmannsharp13]
* [S. Iyengar, G. Leuschke, A. Leykin, Anton, C. Miller, E. Miller, A. Singh, U. Walther,
  *Twenty-four hours of local cohomology*][iyengaretal13]

## Tags

local cohomology, local cohomology modules

## Future work

* Prove that this definition is equivalent to:
    * the right-derived functor definition
    * the characterization as the limit of Koszul homology
    * the characterization as the cohomology of a Cech-like complex
* Establish long exact sequence(s) in local cohomology
-/

open Opposite

open CategoryTheory

open CategoryTheory.Limits

noncomputable section

universe u v v'

namespace localCohomology

variable {R : Type u} [CommRing R] {D : Type v} [SmallCategory D]

def ringModIdeals (I : D ⥤ Ideal R) : D ⥤ ModuleCat.{u} R where
  obj t := ModuleCat.of R <| R ⧸ I.obj t
  map w := ModuleCat.ofHom <| Submodule.mapQ _ _ LinearMap.id (I.map w).down.down

def diagram (I : D ⥤ Ideal R) (i : ℕ) : Dᵒᵖ ⥤ ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  (ringModIdeals I).op ⋙ Ext R (ModuleCat.{u} R) i

end

variable {R : Type max u v} [CommRing R] {D : Type v} [SmallCategory D]

lemma hasColimitDiagram (I : D ⥤ Ideal R) (i : ℕ) :
    HasColimit (diagram I i) := inferInstance

def ofDiagram (I : D ⥤ Ideal R) (i : ℕ) : ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} R :=
  have := hasColimitDiagram.{u, v} I i
  colimit (diagram I i)

end

variable {R : Type max u v v'} [CommRing R] {D : Type v} [SmallCategory D]

variable {E : Type v'} [SmallCategory E] (I' : E ⥤ D) (I : D ⥤ Ideal R)

def diagramComp (i : ℕ) : diagram (I' ⋙ I) i ≅ I'.op ⋙ diagram I i :=
  Iso.refl _
