/-
Extracted from CategoryTheory/Abelian/Projective/Extend.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Projective resolutions as cochain complexes indexed by the integers

Given a projective resolution `R` of an object `X` in an abelian category `C`,
we define `R.cochainComplex : CochainComplex C ℤ`, which is the extension
of `R.complex : ChainComplex C ℕ`, and the quasi-isomorphism
`R.π' : R.cochainComplex ⟶ (CochainComplex.singleFunctor C 0).obj X`.

-/

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

namespace ProjectiveResolution

variable [HasZeroObject C] [Preadditive C] {X : C}
  (R : ProjectiveResolution X)

noncomputable def cochainComplex : CochainComplex C ℤ :=
  R.complex.extend ComplexShape.embeddingDownNat

noncomputable def cochainComplexXIso (n : ℤ) (k : ℕ) (h : -k = n := by lia) :
    R.cochainComplex.X n ≅ R.complex.X k :=
  HomologicalComplex.extendXIso _ _ h
