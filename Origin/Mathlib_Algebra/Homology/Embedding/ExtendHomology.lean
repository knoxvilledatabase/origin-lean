/-
Extracted from Algebra/Homology/Embedding/ExtendHomology.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Homology of the extension of a homological complex

Given an embedding `e : c.Embedding c'` and `K : HomologicalComplex C c`, we shall
compute the homology of `K.extend e`. In degrees that are not in the image of `e.f`,
the homology is obviously zero. When `e.f j = j`, we construct an isomorphism
`(K.extend e).homology j' ≅ K.homology j`.

-/

open CategoryTheory Limits Category

namespace HomologicalComplex

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]
  [HasZeroObject C]

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

namespace extend

section HomologyData

variable {i j k : ι} {i' j' k' : ι'} (hj' : e.f j = j')
  (hi : c.prev j = i) (hi' : c'.prev j' = i') (hk : c.next j = k) (hk' : c'.next j' = k')

include hk hk' in

lemma comp_d_eq_zero_iff ⦃W : C⦄ (φ : W ⟶ K.X j) :
    φ ≫ K.d j k = 0 ↔ φ ≫ (K.extendXIso e hj').inv ≫ (K.extend e).d j' k' = 0 := by
  by_cases hjk : c.Rel j k
  · have hk' : e.f k = k' := by rw [← hk', ← hj', c'.next_eq' (e.rel hjk)]
    rw [K.extend_d_eq e hj' hk', Iso.inv_hom_id_assoc,
      ← cancel_mono (K.extendXIso e hk').inv, zero_comp, assoc]
  · simp only [K.shape _ _ hjk, comp_zero, true_iff]
    rw [K.extend_d_from_eq_zero e j' k' j hj', comp_zero, comp_zero]
    rw [hk]
    exact hjk

include hi hi' in

lemma d_comp_eq_zero_iff ⦃W : C⦄ (φ : K.X j ⟶ W) :
    K.d i j ≫ φ = 0 ↔ (K.extend e).d i' j' ≫ (K.extendXIso e hj').hom ≫ φ = 0 := by
  by_cases hij : c.Rel i j
  · have hi' : e.f i = i' := by rw [← hi', ← hj', c'.prev_eq' (e.rel hij)]
    rw [K.extend_d_eq e hi' hj', assoc, assoc, Iso.inv_hom_id_assoc,
      ← cancel_epi (K.extendXIso e hi').hom, comp_zero]
  · simp only [K.shape _ _ hij, zero_comp, true_iff]
    rw [K.extend_d_to_eq_zero e i' j' j hj', zero_comp]
    rw [hi]
    exact hij

namespace leftHomologyData

variable (cone : KernelFork (K.d j k)) (hcone : IsLimit cone)
