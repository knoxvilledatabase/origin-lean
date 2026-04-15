/-
Extracted from Algebra/Homology/Embedding/TruncGEHomology.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # The homology of a canonical truncation

Given an embedding of complex shapes `e : Embedding c c'`,
we relate the homology of `K : HomologicalComplex C c'` and of
`K.truncGE e : HomologicalComplex C c'`.

The main result is that `K.πTruncGE e : K ⟶ K.truncGE e` induces a
quasi-isomorphism in degree `e.f i` for all `i`. (Note that the complex
`K.truncGE e` is exact in degrees that are not in the image of `e.f`.)

-/

open CategoryTheory Category Limits

namespace HomologicalComplex

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]
  (K L : HomologicalComplex C c') (φ : K ⟶ L) (e : c.Embedding c') [e.IsTruncGE]
  [∀ i', K.HasHomology i'] [∀ i', L.HasHomology i']

namespace truncGE'

variable (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)

set_option backward.isDefEq.respectTransparency false in

include hi hk in

lemma hasHomology_sc'_of_not_mem_boundary (hj : ¬ e.BoundaryGE j) :
    ((K.truncGE' e).sc' i j k).HasHomology := by
  have : (K.restriction e).HasHomology j :=
    restriction.hasHomology K e i j k hi hk rfl rfl rfl
      (e.prev_f_of_not_boundaryGE hi hj) (e.next_f hk)
  have := ShortComplex.hasHomology_of_iso ((K.restriction e).isoSc' i j k hi hk)
  let φ := (shortComplexFunctor' C c i j k).map (K.restrictionToTruncGE' e)
  have : Epi φ.τ₁ := by dsimp [φ]; infer_instance
  have : IsIso φ.τ₂ := K.isIso_restrictionToTruncGE' e j hj
  have : IsIso φ.τ₃ := K.isIso_restrictionToTruncGE' e k (e.not_boundaryGE_next' hj hk)
  exact ShortComplex.hasHomology_of_epi_of_isIso_of_mono φ

lemma hasHomology_of_not_mem_boundary (hj : ¬ e.BoundaryGE j) :
    (K.truncGE' e).HasHomology j :=
  hasHomology_sc'_of_not_mem_boundary K e _ j _ rfl rfl hj

set_option backward.isDefEq.respectTransparency false in

lemma quasiIsoAt_restrictionToTruncGE' (hj : ¬ e.BoundaryGE j)
    [(K.restriction e).HasHomology j] [(K.truncGE' e).HasHomology j] :
    QuasiIsoAt (K.restrictionToTruncGE' e) j := by
  rw [quasiIsoAt_iff]
  let φ := (shortComplexFunctor C c j).map (K.restrictionToTruncGE' e)
  have : Epi φ.τ₁ := by dsimp [φ]; infer_instance
  have : IsIso φ.τ₂ := K.isIso_restrictionToTruncGE' e j hj
  have : IsIso φ.τ₃ := K.isIso_restrictionToTruncGE' e _ (e.not_boundaryGE_next' hj rfl)
  exact ShortComplex.quasiIso_of_epi_of_isIso_of_mono φ

variable {j' : ι'} (hj' : e.f j = j') (hj : e.BoundaryGE j)

lemma homologyι_truncGE'XIsoOpcycles_inv_d :
    (K.homologyι j' ≫ (K.truncGE'XIsoOpcycles e hj' hj).inv) ≫ (K.truncGE' e).d j k = 0 := by
  by_cases hjk : c.Rel j k
  · rw [K.truncGE'_d_eq_fromOpcycles e hjk hj' rfl hj, assoc, Iso.inv_hom_id_assoc,
    homologyι_comp_fromOpcycles_assoc, zero_comp]
  · rw [shape _ _ _ hjk, comp_zero]

noncomputable def isLimitKernelFork :
    IsLimit (KernelFork.ofι _ (homologyι_truncGE'XIsoOpcycles_inv_d K e j k hj' hj)) := by
  have hk' : c'.next j' = e.f k := by simpa only [hj'] using e.next_f hk
  by_cases hjk : c.Rel j k
  · let e : parallelPair ((K.truncGE' e).d j k) 0 ≅
        parallelPair (K.fromOpcycles j' (e.f k)) 0 :=
      parallelPair.ext (K.truncGE'XIsoOpcycles e hj' hj)
        (K.truncGE'XIso e rfl (e.not_boundaryGE_next hjk))
        (by simp [K.truncGE'_d_eq_fromOpcycles e hjk hj' rfl hj]) (by simp)
    exact (IsLimit.postcomposeHomEquiv e _).1
      (IsLimit.ofIsoLimit (K.homologyIsKernel _ _ hk')
      (Fork.ext (Iso.refl _) (by simp [e, Fork.ι])))
  · have := K.isIso_homologyι _ _ hk'
      (shape _ _ _ (by simpa only [← hj', e.rel_iff] using hjk))
    exact IsLimit.ofIsoLimit (KernelFork.IsLimit.ofId _ (shape _ _ _ hjk))
      (Fork.ext ((truncGE'XIsoOpcycles K e hj' hj) ≪≫ (asIso (K.homologyι j')).symm))

noncomputable def homologyData :
    ((K.truncGE' e).sc' i j k).HomologyData :=
  ShortComplex.HomologyData.ofIsLimitKernelFork _
    ((K.truncGE' e).shape _ _ (fun hij => e.not_boundaryGE_next hij hj)) _
    (isLimitKernelFork K e j k hk hj' hj)
