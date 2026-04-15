/-
Extracted from CategoryTheory/Sums/Associator.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Associator for binary disjoint union of categories.

The associator functor `((C ⊕ D) ⊕ E) ⥤ (C ⊕ (D ⊕ E))` and its inverse form an equivalence.
-/

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory

open Sum Functor

namespace CategoryTheory.sum

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]
  (E : Type u₃) [Category.{v₃} E]

def associator : (C ⊕ D) ⊕ E ⥤ C ⊕ (D ⊕ E) :=
  (inl_ C (D ⊕ E) |>.sum' <| inl_ D E ⋙ inr_ C (D ⊕ E)).sum' <| inr_ D E ⋙ inr_ C (D ⊕ E)
