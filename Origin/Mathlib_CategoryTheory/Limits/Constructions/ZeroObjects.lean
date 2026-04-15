/-
Extracted from CategoryTheory/Limits/Constructions/ZeroObjects.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Limits involving zero objects

Binary products and coproducts with a zero object always exist,
and pullbacks/pushouts over a zero object are products/coproducts.
-/

noncomputable section

open CategoryTheory

variable {C : Type*} [Category* C]

namespace CategoryTheory.Limits

variable [HasZeroObject C] [HasZeroMorphisms C]

open ZeroObject

def binaryFanZeroLeft (X : C) : BinaryFan (0 : C) X :=
  BinaryFan.mk 0 (𝟙 X)

def binaryFanZeroLeftIsLimit (X : C) : IsLimit (binaryFanZeroLeft X) :=
  BinaryFan.isLimitMk (fun s => BinaryFan.snd s) (by cat_disch) (by simp)
    (fun s m _ h₂ => by simpa using h₂)

-- INSTANCE (free from Core): hasBinaryProduct_zero_left

def zeroProdIso (X : C) : (0 : C) ⨯ X ≅ X :=
  limit.isoLimitCone ⟨_, binaryFanZeroLeftIsLimit X⟩
