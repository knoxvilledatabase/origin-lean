/-
Extracted from CategoryTheory/Presentable/Presheaf.lean
Genuine: 1 of 5 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Categories of presheaves are locally presentable

If `A` is a locally `κ`-presentable category and `C` is a small category,
we show that `Cᵒᵖ ⥤ A` is also locally `κ`-presentable, under the
additional assumption that `A` has pullbacks (a condition which should
be automatically satisfied (TODO)).

-/

universe w v v' u u'

namespace CategoryTheory

open Opposite Limits

namespace Presheaf

attribute [local simp] freeYonedaHomEquiv_comp in

-- INSTANCE (free from Core): {C

-- INSTANCE (free from Core): {C

lemma isStrongGenerator
    {A : Type u'} [Category.{v'} A] {P : ObjectProperty A} (hP : P.IsStrongGenerator)
    [HasCoproducts.{w} A] [HasPullbacks A] (C : Type w) [SmallCategory C] :
    (ObjectProperty.ofObj (fun (T : C × (Subtype P)) ↦
      freeYoneda T.1 T.2.1)).IsStrongGenerator := by
  rw [ObjectProperty.isStrongGenerator_iff] at hP ⊢
  obtain ⟨hP₁, hP₂⟩ := hP
  refine ⟨Presheaf.isSeparating (C := C) (ι := Subtype P) (S := Subtype.val)
    (by simpa using hP₁),
    fun P₁ P₂ i _ hi ↦ ?_⟩
  rw [NatTrans.isIso_iff_isIso_app]
  rintro ⟨X⟩
  refine hP₂ _ (fun G hG f ↦ ?_)
  obtain ⟨y, rfl⟩ := freeYonedaHomEquiv.surjective f
  obtain ⟨x, rfl⟩ := hi (freeYoneda X G)
    (ObjectProperty.ofObj_apply (fun (T : C × (Subtype P)) ↦
      freeYoneda T.1 T.2.1) ⟨X, G, hG⟩) y
  exact ⟨freeYonedaHomEquiv x, by simp [freeYonedaHomEquiv_comp]⟩

-- INSTANCE (free from Core): {A

-- INSTANCE (free from Core): {A

end Presheaf

end CategoryTheory
