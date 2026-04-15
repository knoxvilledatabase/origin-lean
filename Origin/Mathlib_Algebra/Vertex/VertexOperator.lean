/-
Extracted from Algebra/Vertex/VertexOperator.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Vertex operators
In this file we introduce vertex operators as linear maps to Laurent series.

## Definitions
* `VertexOperator` is an `R`-linear map from an `R`-module `V` to `LaurentSeries V`.
* `VertexOperator.ncoeff` is the coefficient of a vertex operator under normalized indexing.

## TODO
* `HasseDerivative` : A divided-power derivative.
* `Locality` : A weak form of commutativity.
* `Residue products` : A family of products on `VertexOperator R V` parametrized by integers.

## References
* [G. Mason, *Vertex rings and Pierce bundles*][mason2017]
* [A. Matsuo, K. Nagatomo, *On axioms for a vertex algebra and locality of quantum
  fields*][matsuo1997]
-/

noncomputable section

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

abbrev VertexOperator (R : Type*) (V : Type*) [CommRing R] [AddCommGroup V]
    [Module R V] := HVertexOperator ℤ R V V

namespace VertexOperator

open HVertexOperator
