/-
Extracted from AlgebraicTopology/SimplicialSet/AnodyneExtensions/Pairing.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Pairings

In this file, we introduce the definition of a pairing for a subcomplex `A`
of a simplicial set `X`, following the ideas by Sean Moss,
*Another approach to the Kan-Quillen model structure*, who gave a
complete combinatorial characterization of strong (inner) anodyne extensions.
Strong (inner) anodyne extensions are transfinite compositions of pushouts of coproducts
of (inner) horn inclusions, i.e. this is similar to (inner) anodyne extensions but
without the stability property under retracts.

A pairing for `A` consists in the data of a partition of the nondegenerate
simplices of `X` not in `A` into type (I) simplices and type (II) simplices,
and of a bijection between the types of type (I) and type (II) simplices.
Indeed, the main observation is that when we attach a simplex along a horn
inclusion, exactly two nondegenerate simplices are added: this simplex,
and the unique face which is not in the image of the horn. The former shall be
considered as of type (I) and the latter as type (II).

We say that a pairing is *regular* (typeclass `Pairing.IsRegular`) when
- it is proper (`Pairing.IsProper`), i.e. any type (II) simplex is uniquely
  a face of the corresponding type (I) simplex.
- a certain ancestrality relation is well founded.

When these conditions are satisfied, the inclusion `A.ι : A ⟶ X` is
a strong anodyne extension (TODO @joelriou), and the converse is also true
(if `A.ι` is a strong anodyne extension, then there is a regular pairing for `A` (TODO)).

## References
* [Sean Moss, *Another approach to the Kan-Quillen model structure*][moss-2020]

-/

universe u

namespace SSet.Subcomplex

variable {X : SSet.{u}} (A : X.Subcomplex)

structure Pairing where
  /-- the set of type (I) simplices -/
  I : Set A.N
  /-- the set of type (II) simplices -/
  II : Set A.N
  inter : I ∩ II = ∅
  union : I ∪ II = Set.univ
  /-- a bijection from the type (II) simplices to the type (I) simplices -/
  p : II ≃ I

namespace Pairing

variable {A} (P : A.Pairing)

class IsProper where
  isUniquelyCodimOneFace (x : P.II) :
    S.IsUniquelyCodimOneFace x.1.toS (P.p x).1.toS

lemma isUniquelyCodimOneFace [P.IsProper] (x : P.II) :
    S.IsUniquelyCodimOneFace x.1.toS (P.p x).1.toS :=
  IsProper.isUniquelyCodimOneFace x
