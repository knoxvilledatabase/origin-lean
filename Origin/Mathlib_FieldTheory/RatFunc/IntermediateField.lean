/-
Extracted from FieldTheory/RatFunc/IntermediateField.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Intermediate Fields of Rational Function Fields

Results relating `IntermediateField` and `RatFunc`.
-/

variable {K : Type*} [Field K]

namespace RatFunc

open IntermediateField algebraAdjoinAdjoin Polynomial Algebra

variable (f : K⟮X⟯)

theorem adjoin_X : K⟮(X : K⟮X⟯)⟯ = ⊤ :=
  eq_top_iff.mpr fun g _ ↦ (mem_adjoin_simple_iff _ _).mpr ⟨g.num, g.denom, by simp⟩

theorem IntermediateField.adjoin_X (E : IntermediateField K K⟮X⟯) :
    E⟮(X : K⟮X⟯)⟯ = ⊤ := by
  rw [← restrictScalars_eq_top_iff (K := K), IntermediateField.restrictScalars_adjoin,
    _root_.eq_top_iff]
  exact le_trans (le_of_eq RatFunc.adjoin_X.symm) (adjoin.mono _ _ _ (by simp))

noncomputable def IntermediateField.adjoinXEquiv (E : IntermediateField K K⟮X⟯) :
    E⟮(X : K⟮X⟯)⟯ ≃ₐ[E] K⟮X⟯ :=
  (equivOfEq (adjoin_X E)).trans topEquiv

noncomputable abbrev minpolyX (A : Type*) [CommRing A] [Algebra K A] [Algebra K[f] A] : A[X] :=
  f.num.map (algebraMap K A) -
  Polynomial.C (algebraMap K[f] A (⟨f, self_mem_adjoin_singleton K f⟩ : K[f])) *
    f.denom.map (algebraMap K A)

theorem minpolyX_map (A : Type*) [CommRing A] [Algebra K A] [Algebra (Algebra.adjoin K {f}) A]
    (B : Type*) [CommRing B] [Algebra K B] [Algebra K[f] B] [Algebra A B] [IsScalarTower K A B]
    [IsScalarTower K[f] A B] : (f.minpolyX A).map (algebraMap A B) = f.minpolyX B := by
  simp [minpolyX, Polynomial.map_map, ← IsScalarTower.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply]
