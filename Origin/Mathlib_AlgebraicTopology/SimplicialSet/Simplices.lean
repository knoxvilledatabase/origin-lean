/-
Extracted from AlgebraicTopology/SimplicialSet/Simplices.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The preordered type of simplices of a simplicial set

In this file, we define the type `X.S` of simplices of a simplicial set `X`,
where a simplex consists of the data of `dim : ℕ` and `simplex : X _⦋dim⦌`.
We endow this type with a preorder defined by
`x ≤ y ↔ Subcomplex.ofSimplex x.simplex ≤ Subcomplex.ofSimplex y.simplex`.
In particular, as a preordered type, `X.S` is a category, but this is
not what is called "the category of simplices of `X`" in the literature
(and which is `X.Elementsᵒᵖ` in mathlib).

## TODO (@joelriou)

* Extend the `S` structure to define the type of nondegenerate
  simplices of a simplicial set `X`, and also the type of nondegenerate
  simplices of a simplicial set `X` which do not belong to a given subcomplex.

-/

universe u

open CategoryTheory Simplicial

namespace SSet

variable (X : SSet.{u})

structure S where
  /-- the dimension of the simplex -/
  {dim : ℕ}
  /-- the simplex -/
  simplex : X _⦋dim⦌

variable {X}

namespace S

lemma mk_surjective (s : X.S) :
    ∃ (n : ℕ) (x : X _⦋n⦌), s = mk x :=
  ⟨s.dim, s.simplex, rfl⟩

def map {Y : SSet.{u}} (f : X ⟶ Y) (s : X.S) : Y.S :=
  S.mk (f.app _ s.simplex)

lemma dim_eq_of_eq {s t : X.S} (h : s = t) :
    s.dim = t.dim :=
  congr_arg dim h

lemma dim_eq_of_mk_eq {n m : ℕ} {x : X _⦋n⦌} {y : X _⦋m⦌}
    (h : S.mk x = S.mk y) : n = m :=
  dim_eq_of_eq h

variable (s : X.S) {d : ℕ} (hd : s.dim = d)
