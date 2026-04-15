/-
Extracted from CategoryTheory/SmallObject/Iteration/Nonempty.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Existence of the iteration of a successor structure

Given `Φ : SuccStruct C`, we show by transfinite induction
that for any element `j` in a well-ordered set `J`,
the type `Φ.Iteration j` is nonempty.

-/

universe u

namespace CategoryTheory

namespace SmallObject

namespace SuccStruct

open Category Limits

variable {C : Type*} [Category* C] (Φ : SuccStruct C)
  {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  [HasIterationOfShape J C]

namespace Iteration

variable (J) in

def mkOfBot : Φ.Iteration (⊥ : J) where
  F := (Functor.const _).obj Φ.X₀
  obj_bot := rfl
  arrowSucc_eq _ h := by simp at h
  arrowMap_limit _ h₁ h₂ := (h₁.not_isMin (by simpa using h₂)).elim

variable {Φ}

set_option backward.isDefEq.respectTransparency false in

open Functor in

noncomputable def mkOfSucc {j : J} (hj : ¬IsMax j) (iter : Φ.Iteration j) :
    Φ.Iteration (Order.succ j) where
  F := extendToSucc hj iter.F (Φ.toSucc _)
  obj_bot := by rw [extendToSucc_obj_eq _ _ _ _ bot_le, obj_bot]
  arrowSucc_eq i hi₁ := by
    rw [Order.lt_succ_iff_of_not_isMax hj] at hi₁
    obtain hi₁ | rfl := hi₁.lt_or_eq
    · rw [arrowSucc_def, arrowMap_extendToSucc _ _ _ _ _ _ (Order.succ_le_of_lt hi₁),
        ← arrowSucc_def _ _ hi₁, iter.arrowSucc_eq i hi₁,
        extendToSucc_obj_eq hj iter.F (Φ.toSucc _) i hi₁.le]
    · rw [arrowSucc_extendToSucc, toSuccArrow,
        extendToSucc_obj_eq hj iter.F (Φ.toSucc _) i]
  arrowMap_limit i hi hij k hk := by
    have hij' := (Order.IsSuccLimit.le_succ_iff hi).1 hij
    rw [arrowMap_extendToSucc _ _ _ _ _ _ hij', arrowMap_limit _ _ hi _ _ hk]
    congr 1
    apply Arrow.functor_ext
    rintro ⟨k₁, h₁⟩ ⟨k₂, h₂⟩ f
    dsimp
    rw [← arrowMap, ← arrowMap, arrowMap_extendToSucc]
    rfl

namespace mkOfLimit

open Functor

variable {j : J} (hj : Order.IsSuccLimit j) (iter : ∀ (i : J), i < j → Φ.Iteration i)
