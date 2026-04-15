/-
Extracted from CategoryTheory/Preadditive/Schur.lean
Genuine: 3 of 8 | Dissolved: 4 | Infrastructure: 1
-/
import Origin.Core

/-!
# Schur's lemma
We first prove the part of Schur's Lemma that holds in any preadditive category with kernels,
that any nonzero morphism between simple objects
is an isomorphism.

Second, we prove Schur's lemma for `𝕜`-linear categories with finite-dimensional hom spaces,
over an algebraically closed field `𝕜`:
the hom space `X ⟶ Y` between simple objects `X` and `Y` is at most one dimensional,
and is 1-dimensional iff `X` and `Y` are isomorphic.
-/

namespace CategoryTheory

open CategoryTheory.Limits

variable {C : Type*} [Category* C]

variable [Preadditive C]

-- DISSOLVED: mono_of_nonzero_from_simple

-- DISSOLVED: isIso_of_hom_simple

-- DISSOLVED: isIso_iff_nonzero

open scoped Classical in

-- INSTANCE (free from Core): [HasKernels

open Module

variable (𝕜 : Type*) [DivisionRing 𝕜]

theorem finrank_hom_simple_simple_eq_zero_of_not_iso [HasKernels C] [Linear 𝕜 C] {X Y : C}
    [Simple X] [Simple Y] (h : (X ≅ Y) → False) : finrank 𝕜 (X ⟶ Y) = 0 :=
  haveI :=
    subsingleton_of_forall_eq (0 : X ⟶ Y) fun f => by
      have p := not_congr (isIso_iff_nonzero f)
      simp only [Classical.not_not, Ne] at p
      exact p.mp fun _ => h (asIso f)
  finrank_zero_of_subsingleton

end

variable (𝕜 : Type*) [Field 𝕜]

variable [IsAlgClosed 𝕜] [Linear 𝕜 C]

set_option backward.isDefEq.respectTransparency false in

-- DISSOLVED: finrank_endomorphism_eq_one

variable [HasKernels C]

theorem finrank_endomorphism_simple_eq_one (X : C) [Simple X] [FiniteDimensional 𝕜 (X ⟶ X)] :
    finrank 𝕜 (X ⟶ X) = 1 :=
  finrank_endomorphism_eq_one 𝕜 isIso_iff_nonzero

theorem endomorphism_simple_eq_smul_id {X : C} [Simple X] [FiniteDimensional 𝕜 (X ⟶ X)]
    (f : X ⟶ X) : ∃ c : 𝕜, c • 𝟙 X = f :=
  (finrank_eq_one_iff_of_nonzero' (𝟙 X) (id_nonzero X)).mp (finrank_endomorphism_simple_eq_one 𝕜 X)
    f
