/-
Extracted from CategoryTheory/Abelian/Injective/Extend.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Injective resolutions as cochain complexes indexed by the integers

Given an injective resolution `R` of an object `X` in an abelian category `C`,
we define `R.cochainComplex : CochainComplex C ℤ`, which is the extension
of `R.cocomplex : CochainComplex C ℕ`, and the quasi-isomorphism
`R.ι' : (CochainComplex.singleFunctor C 0).obj X ⟶ R.cochainComplex`.

-/

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

namespace InjectiveResolution

variable [HasZeroObject C] [Preadditive C] {X : C}
  (R : InjectiveResolution X)

noncomputable def cochainComplex : CochainComplex C ℤ :=
  R.cocomplex.extend ComplexShape.embeddingUpNat

-- INSTANCE (free from Core): :

noncomputable def cochainComplexXIso (n : ℤ) (k : ℕ) (h : k = n) :
    R.cochainComplex.X n ≅ R.cocomplex.X k :=
  HomologicalComplex.extendXIso _ _ h
