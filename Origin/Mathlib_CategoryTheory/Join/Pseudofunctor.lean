/-
Extracted from CategoryTheory/Join/Pseudofunctor.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Pseudofunctoriality of categorical joins

In this file, we promote the join construction to two pseudofunctors
`Join.pseudofunctorLeft` and `Join.pseudofunctorRight`, expressing its pseudofunctoriality in
each variable.

-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Join

open Bicategory Functor

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]

variable (A) in

def mapCompRight (F : B ⥤ C) (G : C ⥤ D) :
    mapPair (𝟭 A) (F ⋙ G) ≅ mapPair (𝟭 A) F ⋙ mapPair (𝟭 A) G :=
  mapIsoWhiskerRight (Functor.leftUnitor _).symm _ ≪≫ mapPairComp (𝟭 A) F (𝟭 A) G

variable (D) in

def mapCompLeft (F : A ⥤ B) (G : B ⥤ C) :
    mapPair (F ⋙ G) (𝟭 D) ≅ mapPair F (𝟭 D) ⋙ mapPair G (𝟭 D) :=
  mapIsoWhiskerLeft _ (Functor.leftUnitor _).symm ≪≫ mapPairComp F (𝟭 D) G (𝟭 D)

variable (A) in
