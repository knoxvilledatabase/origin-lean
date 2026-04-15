/-
Extracted from Algebra/Homology/HomologicalComplexAbelian.lean
Genuine: 4 of 13 | Dissolved: 0 | Infrastructure: 9
-/
import Origin.Core

/-! # THe category of homological complexes is abelian

If `C` is an abelian category, then `HomologicalComplex C c` is an abelian
category for any complex shape `c : ComplexShape ι`.

We also obtain that a short complex in `HomologicalComplex C c`
is exact (resp. short exact) iff degreewise it is so.

-/

open CategoryTheory Category Limits

namespace HomologicalComplex

variable {C ι : Type*} {c : ComplexShape ι} [Category* C]

variable [Abelian C]

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

variable (S : ShortComplex (HomologicalComplex C c))

lemma exact_of_degreewise_exact (hS : ∀ (i : ι), (S.map (eval C c i)).Exact) :
    S.Exact := by
  simp only [ShortComplex.exact_iff_isZero_homology] at hS ⊢
  rw [IsZero.iff_id_eq_zero]
  ext i
  apply (IsZero.of_iso (hS i) (S.mapHomologyIso (eval C c i)).symm).eq_of_src

lemma shortExact_of_degreewise_shortExact
    (hS : ∀ (i : ι), (S.map (eval C c i)).ShortExact) :
    S.ShortExact where
  mono_f := mono_of_mono_f _ (fun i => (hS i).mono_f)
  epi_g := epi_of_epi_f _ (fun i => (hS i).epi_g)
  exact := exact_of_degreewise_exact S (fun i => (hS i).exact)

lemma exact_iff_degreewise_exact :
    S.Exact ↔ ∀ (i : ι), (S.map (eval C c i)).Exact := by
  constructor
  · intro hS i
    exact hS.map (eval C c i)
  · exact exact_of_degreewise_exact S

lemma shortExact_iff_degreewise_shortExact :
    S.ShortExact ↔ ∀ (i : ι), (S.map (eval C c i)).ShortExact := by
  constructor
  · intro hS i
    have := hS.mono_f
    have := hS.epi_g
    exact hS.map (eval C c i)
  · exact shortExact_of_degreewise_shortExact S

end

variable [HasZeroMorphisms C] [HasZeroObject C] [DecidableEq ι]

-- INSTANCE (free from Core): (i

-- INSTANCE (free from Core): (i

end

end HomologicalComplex

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

variable {D : Type*} [Category* D] [HasZeroMorphisms D]

variable (F : C ⥤ D) {ι : Type*} (c : ComplexShape ι)

-- INSTANCE (free from Core): [F.PreservesZeroMorphisms]

-- INSTANCE (free from Core): [F.PreservesZeroMorphisms]

-- INSTANCE (free from Core): [HasFiniteLimits

-- INSTANCE (free from Core): [HasFiniteColimits

end CategoryTheory
