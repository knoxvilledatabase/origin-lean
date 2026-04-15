/-
Extracted from Order/Filter/FilterProduct.lean
Genuine: 3 of 8 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
# Ultraproducts

If `φ` is an ultrafilter, then the space of germs of functions `f : α → β` at `φ` is called
the *ultraproduct*. In this file we prove properties of ultraproducts that rely on `φ` being an
ultrafilter. Definitions and properties that work for any filter should go to `Order.Filter.Germ`.

## Tags

ultrafilter, ultraproduct
-/

universe u v

variable {α : Type u} {β : Type v} {φ : Ultrafilter α}

namespace Filter

local notation3 "∀* "(...)", "r:(scoped p => Filter.Eventually p (Ultrafilter.toFilter φ)) => r

namespace Germ

open Ultrafilter

local notation "β*" => Germ (φ : Filter α) β

-- INSTANCE (free from Core): instGroupWithZero

-- INSTANCE (free from Core): instDivisionSemiring

-- INSTANCE (free from Core): instDivisionRing

-- INSTANCE (free from Core): instSemifield

-- INSTANCE (free from Core): instField

theorem coe_lt [Preorder β] {f g : α → β} : (f : β*) < g ↔ ∀* x, f x < g x := by
  simp only [lt_iff_le_not_ge, eventually_and, coe_le, eventually_not, EventuallyLE]

theorem coe_pos [Preorder β] [Zero β] {f : α → β} : 0 < (f : β*) ↔ ∀* x, 0 < f x :=
  coe_lt

theorem const_lt [Preorder β] {x y : β} : x < y → (↑x : β*) < ↑y :=
  coe_lt.mpr ∘ liftRel_const
