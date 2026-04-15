/-
Extracted from Algebra/Homology/Embedding/ExtendHomotopy.lean
Genuine: 8 of 8 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The extension functor on the homotopy categories

Given an embedding of complex shapes `e : c.Embedding c'` and a preadditive
category `C`, we define a fully faithful functor
`e.extendHomotopyFunctor C : HomotopyCategory C c ⥤ HomotopyCategory C c'`.

-/

open CategoryTheory Category Limits ZeroObject

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

namespace Homotopy

open HomologicalComplex

variable {C : Type*} [Category* C] [HasZeroObject C] [Preadditive C]
  {K L : HomologicalComplex C c} {f g : K ⟶ L}

namespace extend

variable (e : c.Embedding c') (φ : ∀ i j, K.X i ⟶ L.X j)

noncomputable def homAux (i' j' : Option ι) : extend.X K i' ⟶ extend.X L j' :=
  match i', j' with
  | none, _ => 0
  | _, none => 0
  | some i, some j => φ i j

lemma homAux_eq (i' j' : Option ι) (i j : ι) (hi : i' = some i) (hj : j' = some j) :
    homAux φ i' j' = (extend.XIso K hi).hom ≫ φ i j ≫ (extend.XIso L hj).inv := by
  subst hi hj
  simp [homAux, extend.XIso, extend.X]

noncomputable def hom (i' j' : ι') : (K.extend e).X i' ⟶ (L.extend e).X j' :=
  extend.homAux φ (e.r i') (e.r j')

lemma hom_eq_zero₁ (i' j' : ι') (hi' : ∀ i, e.f i ≠ i') :
    hom e φ i' j' = 0 :=
  (isZero_extend_X _ _ _ hi').eq_of_src _ _

lemma hom_eq_zero₂ (i' j' : ι') (hj' : ∀ j, e.f j ≠ j') :
    hom e φ i' j' = 0 :=
  (isZero_extend_X _ _ _ hj').eq_of_tgt _ _

lemma hom_eq {i' j' : ι'} {i j : ι} (hi : e.f i = i') (hj : e.f j = j') :
    hom e φ i' j' = (K.extendXIso e hi).hom ≫ φ i j ≫ (L.extendXIso e hj).inv :=
  homAux_eq φ (e.r i') (e.r j') i j (e.r_eq_some hi) (e.r_eq_some hj)

end extend

noncomputable def extend (h : Homotopy f g) (e : c.Embedding c') [e.IsRelIff] :
    Homotopy (extendMap f e) (extendMap g e) where
  hom := extend.hom e h.hom
  comm i' := by
    by_cases hi' : ∃ i, e.f i = i'
    · obtain ⟨i, rfl⟩ := hi'
      rw [extendMap_f _ _ rfl, extendMap_f _ _ rfl, h.comm i, Preadditive.add_comp,
        Preadditive.add_comp, Preadditive.comp_add, Preadditive.comp_add, add_left_inj]
      congr 1
      · by_cases hi : c.Rel i (c.next i)
        · have hi' : c'.Rel (e.f i) (e.f (c.next i)) := by rwa [e.rel_iff]
          simp [dNext_eq _ hi, dNext_eq _ hi', extend.hom_eq _ _ rfl rfl,
            extend_d_eq _ _ rfl rfl]
        · rw [dNext_eq_zero _ _ hi]
          by_cases hi' : c'.Rel (e.f i) (c'.next (e.f i))
          · simp [dNext_eq _ hi', K.extend_d_from_eq_zero _ _ _ _ rfl hi]
          · simp [dNext_eq_zero _ _ hi']
      · by_cases hi : c.Rel (c.prev i) i
        · have hi' : c'.Rel (e.f (c.prev i)) (e.f i) := by rwa [e.rel_iff]
          simp [prevD_eq _ hi, prevD_eq _ hi', extend.hom_eq _ _ rfl rfl,
            extend_d_eq _ _ rfl rfl]
        · rw [prevD_eq_zero _ _ hi]
          by_cases hi' : c'.Rel (c'.prev (e.f i)) (e.f i)
          · simp [prevD_eq _ hi', L.extend_d_to_eq_zero _ _ _ _ rfl hi]
          · simp [prevD_eq_zero _ _ hi']
    · exact (isZero_extend_X _ _ _ (by tauto)).eq_of_src _ _
  zero i' j' hij' := by
    by_cases hi' : ∃ i, e.f i = i'
    · obtain ⟨i, rfl⟩ := hi'
      by_cases hj' : ∃ j, e.f j = j'
      · obtain ⟨j, rfl⟩ := hj'
        rw [extend.hom_eq _ _ rfl rfl, h.zero _ _ (by rwa [← e.rel_iff]),
          zero_comp, comp_zero]
      · exact extend.hom_eq_zero₂ _ _ _ _ (by tauto)
    · exact extend.hom_eq_zero₁ _ _ _ _ (by tauto)

lemma extend_hom_eq (h : Homotopy f g) (e : c.Embedding c') [e.IsRelIff]
    {i' j' : ι'} {i j : ι} (hi : e.f i = i') (hj : e.f j = j') :
    (h.extend e).hom i' j' = (K.extendXIso e hi).hom ≫ h.hom i j ≫ (L.extendXIso e hj).inv :=
  extend.hom_eq _ _ _ _
