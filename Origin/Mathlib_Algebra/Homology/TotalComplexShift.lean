/-
Extracted from Algebra/Homology/TotalComplexShift.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Behaviour of the total complex with respect to shifts

There are two ways to shift objects in `HomologicalComplex₂ C (up ℤ) (up ℤ)`:
* by shifting the first indices (and changing signs of horizontal differentials),
  which corresponds to the shift by `ℤ` on `CochainComplex (CochainComplex C ℤ) ℤ`.
* by shifting the second indices (and changing signs of vertical differentials).

These two sorts of shift functors shall be abbreviated as
`HomologicalComplex₂.shiftFunctor₁ C x` and
`HomologicalComplex₂.shiftFunctor₂ C y`.

In this file, for any `K : HomologicalComplex₂ C (up ℤ) (up ℤ)`, we define an isomorphism
`K.totalShift₁Iso x : ((shiftFunctor₁ C x).obj K).total (up ℤ) ≅ (K.total (up ℤ))⟦x⟧`
for any `x : ℤ` (which does not involve signs) and an isomorphism
`K.totalShift₂Iso y : ((shiftFunctor₂ C y).obj K).total (up ℤ) ≅ (K.total (up ℤ))⟦y⟧`
for any `y : ℤ` (which is given by the multiplication by `(p * y).negOnePow` on the
summand in bidegree `(p, q)` of `K`).

Depending on the order of the "composition" of the two isomorphisms
`totalShift₁Iso` and `totalShift₂Iso`, we get
two ways to identify `((shiftFunctor₁ C x).obj ((shiftFunctor₂ C y).obj K)).total (up ℤ)`
and `(K.total (up ℤ))⟦x + y⟧`. The lemma `totalShift₁Iso_trans_totalShift₂Iso` shows that
these two compositions of isomorphisms differ by the sign `(x * y).negOnePow`.

-/

assert_not_exists TwoSidedIdeal

open CategoryTheory Category ComplexShape Limits

namespace HomologicalComplex₂

variable (C : Type*) [Category* C] [Preadditive C]

abbrev shiftFunctor₁ (x : ℤ) :
    HomologicalComplex₂ C (up ℤ) (up ℤ) ⥤ HomologicalComplex₂ C (up ℤ) (up ℤ) :=
  shiftFunctor _ x

abbrev shiftFunctor₂ (y : ℤ) :
    HomologicalComplex₂ C (up ℤ) (up ℤ) ⥤ HomologicalComplex₂ C (up ℤ) (up ℤ) :=
  (shiftFunctor _ y).mapHomologicalComplex _

variable {C}

variable (K L : HomologicalComplex₂ C (up ℤ) (up ℤ)) (f : K ⟶ L)

def shiftFunctor₁XXIso (a x a' : ℤ) (h : a' = a + x) (b : ℤ) :
    (((shiftFunctor₁ C x).obj K).X a).X b ≅ (K.X a').X b := eqToIso (by subst h; rfl)

def shiftFunctor₂XXIso (a b y b' : ℤ) (h : b' = b + y) :
    (((shiftFunctor₂ C y).obj K).X a).X b ≅ (K.X a).X b' := eqToIso (by subst h; rfl)
