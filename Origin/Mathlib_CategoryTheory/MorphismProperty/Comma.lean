/-
Extracted from CategoryTheory/MorphismProperty/Comma.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Subcategories of comma categories defined by morphism properties

Given functors `L : A ⥤ T` and `R : B ⥤ T` and morphism properties `P`, `Q` and `W`
on `T`, `A` and `B` respectively, we define the subcategory `P.Comma L R Q W` of
`Comma L R` where

- objects are objects of `Comma L R` with the structural morphism satisfying `P`, and
- morphisms are morphisms of `Comma L R` where the left morphism satisfies `Q` and the
  right morphism satisfies `W`.

For an object `X : T`, this specializes to `P.Over Q X` which is the subcategory of `Over X`
where the structural morphism satisfies `P` and where the horizontal morphisms satisfy `Q`.
Common examples of the latter are e.g. the category of schemes étale (finite, affine, etc.)
over a base `X`. Here `Q = ⊤`.

## Implementation details

- We provide the general constructor `P.Comma L R Q W` to obtain `Over X` and `Under X` as
  special cases of the more general setup.

- Most results are developed only in the case where `Q = ⊤` and `W = ⊤`, but the definition
  is setup in the general case to allow for a later generalization if needed.

-/

namespace CategoryTheory.MorphismProperty

open Limits

section Comma

variable {A : Type*} [Category* A] {B : Type*} [Category* B] {T : Type*} [Category* T]
  (L : A ⥤ T) (R : B ⥤ T)

lemma costructuredArrow_iso_iff (P : MorphismProperty T) [P.RespectsIso]
    {L : A ⥤ T} {X : T} {f g : CostructuredArrow L X} (e : f ≅ g) :
    P f.hom ↔ P g.hom :=
  P.comma_iso_iff e

lemma over_iso_iff (P : MorphismProperty T) [P.RespectsIso] {X : T} {f g : Over X} (e : f ≅ g) :
    P f.hom ↔ P g.hom :=
  P.comma_iso_iff e

variable {W : MorphismProperty T} {X : T}

def commaObj (W : MorphismProperty T) : ObjectProperty (Comma L R) :=
  fun f ↦ W f.hom
