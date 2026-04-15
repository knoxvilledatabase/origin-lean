/-
Extracted from LinearAlgebra/Basis/VectorSpace.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Bases in a vector space

This file provides results for bases of a vector space.

Some of these results should be merged with the results on free modules.
We state these results in a separate file to the results on modules to avoid an
import cycle.

## Main statements

* `Basis.ofVectorSpace` states that every vector space has a basis.
* `Module.Free.of_divisionRing` states that every vector space is a free module.

## Tags

basis, bases

-/

open Function Module Set Submodule

variable {ι : Type*} {ι' : Type*} {K : Type*} {V : Type*} {V' : Type*}

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [AddCommGroup V'] [Module K V] [Module K V']

variable {v : ι → V} {s t : Set V} {x y z : V}

open Submodule

namespace Module.Basis

section ExistsBasis

noncomputable def extend (hs : LinearIndepOn K id s) :
    Basis (hs.extend (subset_univ s)) K V :=
  Basis.mk
    (hs.linearIndepOn_extend _).linearIndependent_restrict
    (SetLike.coe_subset_coe.mp <| by simpa using hs.subset_span_extend (subset_univ s))

theorem extend_apply_self (hs : LinearIndepOn K id s) (x : hs.extend _) : Basis.extend hs x = x :=
  Basis.mk_apply _ _ _
