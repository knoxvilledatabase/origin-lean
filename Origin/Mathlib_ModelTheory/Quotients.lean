/-
Extracted from ModelTheory/Quotients.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Quotients of First-Order Structures

This file defines prestructures and quotients of first-order structures.

## Main Definitions

- If `s` is a setoid (equivalence relation) on `M`, a `FirstOrder.Language.Prestructure s` is the
  data for a first-order structure on `M` that will still be a structure when modded out by `s`.
- The structure `FirstOrder.Language.quotientStructure s` is the resulting structure on
  `Quotient s`.
-/

namespace FirstOrder

namespace Language

variable (L : Language) {M : Type*}

open FirstOrder

open Structure

class Prestructure (s : Setoid M) where
  /-- The underlying first-order structure -/
  toStructure : L.Structure M
  fun_equiv : ∀ {n} {f : L.Functions n} (x y : Fin n → M), x ≈ y → funMap f x ≈ funMap f y
  rel_equiv : ∀ {n} {r : L.Relations n} (x y : Fin n → M) (_ : x ≈ y), RelMap r x = RelMap r y

variable {L} {s : Setoid M}

variable [ps : L.Prestructure s]

-- INSTANCE (free from Core): quotientStructure

variable (s)

theorem funMap_quotient_mk' {n : ℕ} (f : L.Functions n) (x : Fin n → M) :
    (funMap f fun i => (⟦x i⟧ : Quotient s)) = ⟦@funMap _ _ ps.toStructure _ f x⟧ := by
  change
    Quotient.map (@funMap L M ps.toStructure n f) Prestructure.fun_equiv (Quotient.finChoice _) =
      _
  rw [Quotient.finChoice_eq, Quotient.map_mk]

theorem relMap_quotient_mk' {n : ℕ} (r : L.Relations n) (x : Fin n → M) :
    (RelMap r fun i => (⟦x i⟧ : Quotient s)) ↔ @RelMap _ _ ps.toStructure _ r x := by
  change
    Quotient.lift (@RelMap L M ps.toStructure n r) Prestructure.rel_equiv (Quotient.finChoice _) ↔
      _
  rw [Quotient.finChoice_eq, Quotient.lift_mk]

theorem Term.realize_quotient_mk' {β : Type*} (t : L.Term β) (x : β → M) :
    (t.realize fun i => (⟦x i⟧ : Quotient s)) = ⟦@Term.realize _ _ ps.toStructure _ x t⟧ := by
  induction t with
  | var => rfl
  | func _ _ ih => simp only [ih, funMap_quotient_mk', Term.realize]

end Language

end FirstOrder
