/-
Extracted from AlgebraicTopology/SimplicialSet/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Simplicial sets

A simplicial set is just a simplicial object in `Type`,
i.e. a `Type`-valued presheaf on the simplex category.

(One might be tempted to call these "simplicial types" when working in type-theoretic foundations,
but this would be unnecessarily confusing given the existing notion of a simplicial type in
homotopy type theory.)

-/

universe v u

open CategoryTheory Limits Functor ConcreteCategory

open Simplicial

abbrev SSet : Type (u + 1) :=
  SimplicialObject (Type u)

namespace SSet
