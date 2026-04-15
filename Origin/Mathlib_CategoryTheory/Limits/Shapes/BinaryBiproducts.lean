/-
Extracted from CategoryTheory/Limits/Shapes/BinaryBiproducts.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Binary biproducts

We introduce the notion of binary biproducts.

These are slightly unusual relative to the other shapes in the library,
as they are simultaneously limits and colimits.
(Zero objects are similar; they are "biterminal".)

For results about biproducts in preadditive categories see
`CategoryTheory.Preadditive.Biproducts`.

In a category with zero morphisms, we model the (binary) biproduct of `P Q : C`
using a `BinaryBicone`, which has a cone point `X`,
and morphisms `fst : X ⟶ P`, `snd : X ⟶ Q`, `inl : P ⟶ X` and `inr : X ⟶ Q`,
such that `inl ≫ fst = 𝟙 P`, `inl ≫ snd = 0`, `inr ≫ fst = 0`, and `inr ≫ snd = 𝟙 Q`.
Such a `BinaryBicone` is a biproduct if the cone is a limit cone, and the cocone is a colimit
cocone.

-/

noncomputable section

universe w w' v u

open CategoryTheory Functor

namespace CategoryTheory.Limits

variable {J : Type w}

universe uC' uC uD' uD

variable {C : Type uC} [Category.{uC'} C] [HasZeroMorphisms C]

variable {D : Type uD} [Category.{uD'} D] [HasZeroMorphisms D]

structure BinaryBicone (P Q : C) where
  pt : C
  fst : pt ⟶ P
  snd : pt ⟶ Q
  inl : P ⟶ pt
  inr : Q ⟶ pt
  inl_fst : inl ≫ fst = 𝟙 P := by aesop
  inl_snd : inl ≫ snd = 0 := by aesop
  inr_fst : inr ≫ fst = 0 := by aesop
  inr_snd : inr ≫ snd = 𝟙 Q := by aesop

attribute [inherit_doc BinaryBicone] BinaryBicone.pt BinaryBicone.fst BinaryBicone.snd

  BinaryBicone.inl BinaryBicone.inr BinaryBicone.inl_fst BinaryBicone.inl_snd

  BinaryBicone.inr_fst BinaryBicone.inr_snd

attribute [reassoc (attr := simp)]

  BinaryBicone.inl_fst BinaryBicone.inl_snd BinaryBicone.inr_fst BinaryBicone.inr_snd

structure BinaryBiconeMorphism {P Q : C} (A B : BinaryBicone P Q) where
  /-- A morphism between the two vertex objects of the bicones -/
  hom : A.pt ⟶ B.pt
  /-- The triangle consisting of the two natural transformations and `hom` commutes -/
  wfst : hom ≫ B.fst = A.fst := by cat_disch
  /-- The triangle consisting of the two natural transformations and `hom` commutes -/
  wsnd : hom ≫ B.snd = A.snd := by cat_disch
  /-- The triangle consisting of the two natural transformations and `hom` commutes -/
  winl : A.inl ≫ hom = B.inl := by cat_disch
  /-- The triangle consisting of the two natural transformations and `hom` commutes -/
  winr : A.inr ≫ hom = B.inr := by cat_disch

attribute [reassoc (attr := simp)] BinaryBiconeMorphism.wfst BinaryBiconeMorphism.wsnd

attribute [reassoc (attr := simp)] BinaryBiconeMorphism.winl BinaryBiconeMorphism.winr
