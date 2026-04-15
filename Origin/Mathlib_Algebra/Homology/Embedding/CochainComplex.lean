/-
Extracted from Algebra/Homology/Embedding/CochainComplex.lean
Genuine: 8 of 10 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Truncations on cochain complexes indexed by the integers.

In this file, we introduce abbreviations for the canonical truncations
`CochainComplex.truncLE`, `CochainComplex.truncGE` of cochain
complexes indexed by `ℤ`, as well as the conditions
`CochainComplex.IsStrictlyLE`, `CochainComplex.IsStrictlyGE`,
`CochainComplex.IsLE`, and `CochainComplex.IsGE`.

-/

open CategoryTheory Category Limits ComplexShape ZeroObject

namespace CochainComplex

variable {C : Type*} [Category* C]

open HomologicalComplex

section HasZeroMorphisms

variable [HasZeroMorphisms C] (K L : CochainComplex C ℤ) (φ : K ⟶ L) (e : K ≅ L)

variable [HasZeroObject C] [∀ i, K.HasHomology i] [∀ i, L.HasHomology i]

noncomputable abbrev truncLE (n : ℤ) : CochainComplex C ℤ :=
  HomologicalComplex.truncLE K (embeddingUpIntLE n)

noncomputable abbrev truncGE (n : ℤ) : CochainComplex C ℤ :=
  HomologicalComplex.truncGE K (embeddingUpIntGE n)

noncomputable def ιTruncLE (n : ℤ) : K.truncLE n ⟶ K :=
  HomologicalComplex.ιTruncLE K (embeddingUpIntLE n)

noncomputable def πTruncGE (n : ℤ) : K ⟶ K.truncGE n :=
  HomologicalComplex.πTruncGE K (embeddingUpIntGE n)

lemma quasiIsoAt_ιTruncLE (n q : ℤ) (hq : q ≤ n) :
    QuasiIsoAt (K.ιTruncLE n) q := by
  obtain ⟨k, rfl⟩ := Int.le.dest hq
  exact HomologicalComplex.quasiIsoAt_ιTruncLE (j := k) _ _ (by simp)

lemma quasiIsoAt_πTruncGE (n q : ℤ) (hq : n ≤ q) :
    QuasiIsoAt (K.πTruncGE n) q := by
  obtain ⟨k, rfl⟩ := Int.le.dest hq
  exact HomologicalComplex.quasiIsoAt_πTruncGE (j := k) _ _ (by simp)

-- INSTANCE (free from Core): (n

-- INSTANCE (free from Core): (n

variable {K L}

noncomputable abbrev truncLEMap (n : ℤ) : K.truncLE n ⟶ L.truncLE n :=
  HomologicalComplex.truncLEMap φ (embeddingUpIntLE n)

noncomputable abbrev truncGEMap (n : ℤ) : K.truncGE n ⟶ L.truncGE n :=
  HomologicalComplex.truncGEMap φ (embeddingUpIntGE n)
