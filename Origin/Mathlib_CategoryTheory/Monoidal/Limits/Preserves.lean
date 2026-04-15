/-
Extracted from CategoryTheory/Monoidal/Limits/Preserves.lean
Genuine: 4 of 6 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Miscellany about preservation of (co)limits in monoidal categories

This file records some `PreservesColimits` instances on tensor products in monoidal categories. -/

namespace CategoryTheory.MonoidalCategory.Limits

open _root_.CategoryTheory.Limits

variable {C : Type*} [Category* C] [MonoidalCategory C]
  {J : Type*} [Category* J] (F : J ⥤ C)

section Colimits

-- INSTANCE (free from Core): preservesColimit_of_braided_and_preservesColimit_tensor_left

lemma preservesColimit_of_braided_and_preservesColimit_tensor_right
    [BraidedCategory C] (c : C)
    [PreservesColimit F (tensorRight c)] :
    PreservesColimit F (tensorLeft c) :=
  preservesColimit_of_natIso F (BraidedCategory.tensorLeftIsoTensorRight c).symm

lemma preservesCoLimit_curriedTensor [h : ∀ c : C, PreservesColimit F (tensorRight c)] :
    PreservesColimit F (curriedTensor C) :=
  preservesColimit_of_evaluation _ _
    (fun c ↦ inferInstanceAs (PreservesColimit F (tensorRight c)))

end Colimits

section Limits

-- INSTANCE (free from Core): preservesLimit_of_braided_and_preservesLimit_tensor_left

lemma preservesLimit_of_braided_and_preservesLimit_tensor_right
    [BraidedCategory C] (c : C)
    [PreservesLimit F (tensorRight c)] :
    PreservesLimit F (tensorLeft c) :=
  preservesLimit_of_natIso F (BraidedCategory.tensorLeftIsoTensorRight c).symm

lemma preservesLimit_curriedTensor [h : ∀ c : C, PreservesLimit F (tensorRight c)] :
    PreservesLimit F (curriedTensor C) :=
  preservesLimit_of_evaluation _ _ <| fun c ↦ inferInstanceAs (PreservesLimit F (tensorRight c))

end Limits

end CategoryTheory.MonoidalCategory.Limits
