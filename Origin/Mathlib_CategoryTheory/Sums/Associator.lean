/-
Extracted from CategoryTheory/Sums/Associator.lean
Genuine: 3 | Conflates: 0 | Dissolved: 0 | Infrastructure: 14
-/
import Origin.Core
import Mathlib.CategoryTheory.Sums.Basic

noncomputable section

/-!
# Associator for binary disjoint union of categories.

The associator functor `((C ⊕ D) ⊕ E) ⥤ (C ⊕ (D ⊕ E))` and its inverse form an equivalence.
-/

universe v u

open CategoryTheory

open Sum

namespace CategoryTheory.sum

variable (C : Type u) [Category.{v} C] (D : Type u) [Category.{v} D] (E : Type u) [Category.{v} E]

def associator : (C ⊕ D) ⊕ E ⥤ C ⊕ (D ⊕ E) where
  obj X :=
    match X with
    | inl (inl X) => inl X
    | inl (inr X) => inr (inl X)
    | inr X => inr (inr X)
  map {X Y} f :=
    match X, Y, f with
    | inl (inl _), inl (inl _), f => f
    | inl (inr _), inl (inr _), f => f
    | inr _, inr _, f => f
  map_id := by rintro ((_|_)|_) <;> rfl
  map_comp := by
    rintro ((_|_)|_) ((_|_)|_) ((_|_)|_) f g <;> first | cases f | cases g | aesop_cat

def inverseAssociator : C ⊕ (D ⊕ E) ⥤ (C ⊕ D) ⊕ E where
  obj X :=
    match X with
    | inl X => inl (inl X)
    | inr (inl X) => inl (inr X)
    | inr (inr X) => inr X
  map {X Y} f :=
    match X, Y, f with
    | inl _, inl _, f => f
    | inr (inl _), inr (inl _), f => f
    | inr (inr _), inr (inr _), f => f
  map_id := by rintro (_|(_|_)) <;> rfl
  map_comp := by
    rintro (_|(_|_)) (_|(_|_)) (_|(_|_)) f g <;> first | cases f | cases g | aesop_cat

@[simps functor inverse]
def associativity : (C ⊕ D) ⊕ E ≌ C ⊕ (D ⊕ E) where
  functor := associator C D E
  inverse := inverseAssociator C D E
  unitIso := NatIso.ofComponents (by rintro ((_ | _) | _) <;> exact Iso.refl _) (by
    rintro ((_ | _) | _) ((_ | _) | _) f <;> first | cases f | aesop_cat)
  counitIso := NatIso.ofComponents (by rintro (_ | (_ | _)) <;> exact Iso.refl _) (by
    rintro (_ | (_ | _)) (_ | (_ | _)) f <;> first | cases f | aesop_cat)

instance associatorIsEquivalence : (associator C D E).IsEquivalence :=
  (by infer_instance : (associativity C D E).functor.IsEquivalence)

instance inverseAssociatorIsEquivalence : (inverseAssociator C D E).IsEquivalence :=
  (by infer_instance : (associativity C D E).inverse.IsEquivalence)

end CategoryTheory.sum
