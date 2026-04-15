/-
Extracted from Algebra/Homology/ShortComplex/Limits.lean
Genuine: 12 of 42 | Dissolved: 0 | Infrastructure: 30
-/
import Origin.Core

/-!
# Limits and colimits in the category of short complexes

In this file, it is shown if a category `C` with zero morphisms has limits
of a certain shape `J`, then it is also the case of the category `ShortComplex C`.

-/

namespace CategoryTheory

open Category Limits Functor

variable {J C : Type*} [Category* J] [Category* C] [HasZeroMorphisms C]
  {F : J ⥤ ShortComplex C}

namespace ShortComplex

def isLimitOfIsLimitπ (c : Cone F)
    (h₁ : IsLimit (π₁.mapCone c)) (h₂ : IsLimit (π₂.mapCone c))
    (h₃ : IsLimit (π₃.mapCone c)) : IsLimit c where
  lift s :=
    { τ₁ := h₁.lift (π₁.mapCone s)
      τ₂ := h₂.lift (π₂.mapCone s)
      τ₃ := h₃.lift (π₃.mapCone s)
      comm₁₂ := h₂.hom_ext (fun j => by
        have eq₁ := h₁.fac (π₁.mapCone s)
        have eq₂ := h₂.fac (π₂.mapCone s)
        have eq₁₂ := fun j => (c.π.app j).comm₁₂
        have eq₁₂' := fun j => (s.π.app j).comm₁₂
        dsimp at eq₁ eq₂ eq₁₂ eq₁₂' ⊢
        rw [assoc, assoc, ← eq₁₂, reassoc_of% eq₁, eq₂, eq₁₂'])
      comm₂₃ := h₃.hom_ext (fun j => by
        have eq₂ := h₂.fac (π₂.mapCone s)
        have eq₃ := h₃.fac (π₃.mapCone s)
        have eq₂₃ := fun j => (c.π.app j).comm₂₃
        have eq₂₃' := fun j => (s.π.app j).comm₂₃
        dsimp at eq₂ eq₃ eq₂₃ eq₂₃' ⊢
        rw [assoc, assoc, ← eq₂₃, reassoc_of% eq₂, eq₃, eq₂₃']) }
  fac s j := by ext <;> apply IsLimit.fac
  uniq s m hm := by
    ext
    · exact h₁.uniq (π₁.mapCone s) _ (fun j => π₁.congr_map (hm j))
    · exact h₂.uniq (π₂.mapCone s) _ (fun j => π₂.congr_map (hm j))
    · exact h₃.uniq (π₃.mapCone s) _ (fun j => π₃.congr_map (hm j))

variable (F)

variable [HasLimit (F ⋙ π₁)] [HasLimit (F ⋙ π₂)] [HasLimit (F ⋙ π₃)]

set_option backward.isDefEq.respectTransparency false in

noncomputable def limitCone : Cone F :=
  Cone.mk (ShortComplex.mk (limMap (whiskerLeft F π₁Toπ₂)) (limMap (whiskerLeft F π₂Toπ₃))
      (by cat_disch))
    { app := fun j => Hom.mk (limit.π _ _) (limit.π _ _) (limit.π _ _)
        (by simp) (by simp)
      naturality := fun _ _ f => by
        ext <;> simp [← limit.w _ f] }

set_option backward.isDefEq.respectTransparency false in

noncomputable def isLimitπ₁MapConeLimitCone : IsLimit (π₁.mapCone (limitCone F)) :=
  (IsLimit.ofIsoLimit (limit.isLimit _) (Cone.ext (Iso.refl _) (by cat_disch)))

set_option backward.isDefEq.respectTransparency false in

noncomputable def isLimitπ₂MapConeLimitCone : IsLimit (π₂.mapCone (limitCone F)) :=
  (IsLimit.ofIsoLimit (limit.isLimit _) (Cone.ext (Iso.refl _) (by cat_disch)))

set_option backward.isDefEq.respectTransparency false in

noncomputable def isLimitπ₃MapConeLimitCone : IsLimit (π₃.mapCone (limitCone F)) :=
  (IsLimit.ofIsoLimit (limit.isLimit _) (Cone.ext (Iso.refl _) (by cat_disch)))

noncomputable def isLimitLimitCone : IsLimit (limitCone F) :=
  isLimitOfIsLimitπ _ (isLimitπ₁MapConeLimitCone F)
    (isLimitπ₂MapConeLimitCone F) (isLimitπ₃MapConeLimitCone F)

-- INSTANCE (free from Core): hasLimit_of_hasLimitπ

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

end

variable [HasLimitsOfShape J C]

-- INSTANCE (free from Core): hasLimitsOfShape

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

end

variable [HasFiniteLimits C]

-- INSTANCE (free from Core): hasFiniteLimits

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

end

variable [HasLimitsOfShape WalkingCospan C]

-- INSTANCE (free from Core): preservesMonomorphisms_π₁

-- INSTANCE (free from Core): preservesMonomorphisms_π₂

-- INSTANCE (free from Core): preservesMonomorphisms_π₃

end

def isColimitOfIsColimitπ (c : Cocone F)
    (h₁ : IsColimit (π₁.mapCocone c)) (h₂ : IsColimit (π₂.mapCocone c))
    (h₃ : IsColimit (π₃.mapCocone c)) : IsColimit c where
  desc s :=
    { τ₁ := h₁.desc (π₁.mapCocone s)
      τ₂ := h₂.desc (π₂.mapCocone s)
      τ₃ := h₃.desc (π₃.mapCocone s)
      comm₁₂ := h₁.hom_ext (fun j => by
        have eq₁ := h₁.fac (π₁.mapCocone s)
        have eq₂ := h₂.fac (π₂.mapCocone s)
        have eq₁₂ := fun j => (c.ι.app j).comm₁₂
        have eq₁₂' := fun j => (s.ι.app j).comm₁₂
        dsimp at eq₁ eq₂ eq₁₂ eq₁₂' ⊢
        rw [reassoc_of% (eq₁ j), eq₁₂', reassoc_of% eq₁₂, eq₂])
      comm₂₃ := h₂.hom_ext (fun j => by
        have eq₂ := h₂.fac (π₂.mapCocone s)
        have eq₃ := h₃.fac (π₃.mapCocone s)
        have eq₂₃ := fun j => (c.ι.app j).comm₂₃
        have eq₂₃' := fun j => (s.ι.app j).comm₂₃
        dsimp at eq₂ eq₃ eq₂₃ eq₂₃' ⊢
        rw [reassoc_of% (eq₂ j), eq₂₃', reassoc_of% eq₂₃, eq₃]) }
  fac s j := by
    ext
    · apply IsColimit.fac h₁
    · apply IsColimit.fac h₂
    · apply IsColimit.fac h₃
  uniq s m hm := by
    ext
    · exact h₁.uniq (π₁.mapCocone s) _ (fun j => π₁.congr_map (hm j))
    · exact h₂.uniq (π₂.mapCocone s) _ (fun j => π₂.congr_map (hm j))
    · exact h₃.uniq (π₃.mapCocone s) _ (fun j => π₃.congr_map (hm j))

variable (F)

variable [HasColimit (F ⋙ π₁)] [HasColimit (F ⋙ π₂)] [HasColimit (F ⋙ π₃)]

set_option backward.isDefEq.respectTransparency false in

noncomputable def colimitCocone : Cocone F :=
  Cocone.mk (ShortComplex.mk (colimMap (whiskerLeft F π₁Toπ₂)) (colimMap (whiskerLeft F π₂Toπ₃))
      (by cat_disch))
    { app := fun j => Hom.mk (colimit.ι (F ⋙ π₁) _) (colimit.ι (F ⋙ π₂) _)
        (colimit.ι (F ⋙ π₃) _) (by simp) (by simp)
      naturality := fun _ _ f => by
        ext
        · simp [← colimit.w (F ⋙ π₁) f]
        · simp [← colimit.w (F ⋙ π₂) f]
        · simp [← colimit.w (F ⋙ π₃) f] }

set_option backward.isDefEq.respectTransparency false in

noncomputable def isColimitπ₁MapCoconeColimitCocone :
    IsColimit (π₁.mapCocone (colimitCocone F)) :=
  (IsColimit.ofIsoColimit (colimit.isColimit _) (Cocone.ext (Iso.refl _) (by cat_disch)))

set_option backward.isDefEq.respectTransparency false in

noncomputable def isColimitπ₂MapCoconeColimitCocone :
    IsColimit (π₂.mapCocone (colimitCocone F)) :=
  (IsColimit.ofIsoColimit (colimit.isColimit _) (Cocone.ext (Iso.refl _) (by cat_disch)))

set_option backward.isDefEq.respectTransparency false in

noncomputable def isColimitπ₃MapCoconeColimitCocone :
    IsColimit (π₃.mapCocone (colimitCocone F)) :=
  (IsColimit.ofIsoColimit (colimit.isColimit _) (Cocone.ext (Iso.refl _) (by cat_disch)))

noncomputable def isColimitColimitCocone : IsColimit (colimitCocone F) :=
  isColimitOfIsColimitπ _ (isColimitπ₁MapCoconeColimitCocone F)
    (isColimitπ₂MapCoconeColimitCocone F) (isColimitπ₃MapCoconeColimitCocone F)

-- INSTANCE (free from Core): hasColimit_of_hasColimitπ

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

end

variable [HasColimitsOfShape J C]

-- INSTANCE (free from Core): hasColimitsOfShape

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

end

variable [HasFiniteColimits C]

-- INSTANCE (free from Core): hasFiniteColimits

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

end

variable [HasColimitsOfShape WalkingSpan C]

-- INSTANCE (free from Core): preservesEpimorphisms_π₁

-- INSTANCE (free from Core): preservesEpimorphisms_π₂

-- INSTANCE (free from Core): preservesEpimorphisms_π₃

end

end ShortComplex

end CategoryTheory
