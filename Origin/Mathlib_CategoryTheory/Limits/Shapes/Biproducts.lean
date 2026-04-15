/-
Extracted from CategoryTheory/Limits/Shapes/Biproducts.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Biproducts and binary biproducts

We introduce the notion of (finite) biproducts.
Binary biproducts are defined in `CategoryTheory.Limits.Shapes.BinaryBiproducts`.

These are slightly unusual relative to the other shapes in the library,
as they are simultaneously limits and colimits.
(Zero objects are similar; they are "biterminal".)

For results about biproducts in preadditive categories see
`CategoryTheory.Preadditive.Biproducts`.

For biproducts indexed by a `Fintype J`, a `bicone` consists of a cone point `X`
and morphisms `π j : X ⟶ F j` and `ι j : F j ⟶ X` for each `j`,
such that `ι j ≫ π j'` is the identity when `j = j'` and zero otherwise.

## Notation
As `⊕` is already taken for the sum of types, we introduce the notation `X ⊞ Y` for
a binary biproduct. We introduce `⨁ f` for the indexed biproduct.

## Implementation notes

Prior to https://github.com/leanprover-community/mathlib3/pull/14046,
`HasFiniteBiproducts` required a `DecidableEq` instance on the indexing type.
As this had no pay-off (everything about limits is non-constructive in mathlib),
and occasional cost
(constructing decidability instances appropriate for constructions involving the indexing type),
we made everything classical.
-/

noncomputable section

universe w w' v u

open CategoryTheory Functor

namespace CategoryTheory.Limits

variable {J : Type w}

universe uC' uC uD' uD

variable {C : Type uC} [Category.{uC'} C] [HasZeroMorphisms C]

variable {D : Type uD} [Category.{uD'} D] [HasZeroMorphisms D]

open scoped Classical in

structure Bicone (F : J → C) where
  pt : C
  π : ∀ j, pt ⟶ F j
  ι : ∀ j, F j ⟶ pt
  ι_π : ∀ j j', ι j ≫ π j' =
    if h : j = j' then eqToHom (congrArg F h) else 0 := by aesop

attribute [inherit_doc Bicone] Bicone.pt Bicone.π Bicone.ι Bicone.ι_π
