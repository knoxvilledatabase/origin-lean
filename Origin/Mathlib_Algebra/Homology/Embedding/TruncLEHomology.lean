/-
Extracted from Algebra/Homology/Embedding/TruncLEHomology.lean
Genuine: 5 of 8 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-! # The homology of a canonical truncation

Given an embedding of complex shapes `e : Embedding c c'`,
we relate the homology of `K : HomologicalComplex C c'` and of
`K.truncLE e : HomologicalComplex C c'`.

The main result is that `K.ιTruncLE e : K.truncLE e ⟶ K` induces a
quasi-isomorphism in degree `e.f i` for all `i`. (Note that the complex
`K.truncLE e` is exact in degrees that are not in the image of `e.f`.)

All the results are obtained by dualising the results in the file `Embedding.TruncGEHomology`.

Moreover, if `C` is an abelian category, we introduce the cokernel
sequence `K.shortComplexTruncLE e` of the monomorphism `K.ιTruncLE e`.

-/

open CategoryTheory Category Limits

namespace HomologicalComplex

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C]

variable [HasZeroMorphisms C] (K L : HomologicalComplex C c') (φ : K ⟶ L) (e : c.Embedding c')
  [e.IsTruncLE] [∀ i', K.HasHomology i'] [∀ i', L.HasHomology i']

namespace truncLE'

set_option backward.isDefEq.respectTransparency false in

lemma quasiIsoAt_truncLE'ToRestriction (j : ι) (hj : ¬ e.BoundaryLE j)
    [(K.restriction e).HasHomology j] [(K.truncLE' e).HasHomology j] :
    QuasiIsoAt (K.truncLE'ToRestriction e) j := by
  dsimp only [truncLE'ToRestriction]
  have : (K.op.restriction e.op).HasHomology j :=
    inferInstanceAs ((K.restriction e).op.HasHomology j)
  rw [quasiIsoAt_unopFunctor_map_iff]
  exact truncGE'.quasiIsoAt_restrictionToTruncGE' K.op e.op j (by simpa)

-- INSTANCE (free from Core): truncLE'_hasHomology

end truncLE'

variable [HasZeroObject C]

-- INSTANCE (free from Core): (i'

lemma quasiIsoAt_ιTruncLE {j : ι} {j' : ι'} (hj' : e.f j = j') :
    QuasiIsoAt (K.ιTruncLE e) j' := by
  have := K.op.quasiIsoAt_πTruncGE e.op hj'
  exact inferInstanceAs (QuasiIsoAt ((unopFunctor _ _).map (K.op.πTruncGE e.op).op) j')

-- INSTANCE (free from Core): (i

lemma quasiIso_ιTruncLE_iff_isSupported :
    QuasiIso (K.ιTruncLE e) ↔ K.IsSupported e := by
  rw [← quasiIso_opFunctor_map_iff, ← isSupported_op_iff]
  exact K.op.quasiIso_πTruncGE_iff_isSupported e.op

lemma acyclic_truncLE_iff_isSupportedOutside :
    (K.truncLE e).Acyclic ↔ K.IsSupportedOutside e := by
  rw [← acyclic_op_iff, ← isSupportedOutside_op_iff]
  exact K.op.acyclic_truncGE_iff_isSupportedOutside e.op

variable {K L}

lemma quasiIso_truncLEMap_iff :
    QuasiIso (truncLEMap φ e) ↔ ∀ (i : ι) (i' : ι') (_ : e.f i = i'), QuasiIsoAt φ i' := by
  rw [← quasiIso_opFunctor_map_iff]
  simp only [← quasiIsoAt_opFunctor_map_iff φ]
  apply quasiIso_truncGEMap_iff

end

variable [Abelian C] (K : HomologicalComplex C c') (e : c.Embedding c') [e.IsTruncLE]
