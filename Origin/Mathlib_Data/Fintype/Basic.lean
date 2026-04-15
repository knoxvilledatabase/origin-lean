/-
Extracted from Data/Fintype/Basic.lean
Genuine: 1 of 5 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Instances for finite types

This file is a collection of basic `Fintype` instances for types such as `Fin`, `Prod` and pi types.
-/

assert_not_exists Monoid

open Function

open Nat

universe u v

variable {α β γ : Type*}

open Finset

-- INSTANCE (free from Core): Fin.fintype

theorem nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fintype α) := by
  rcases Finite.exists_equiv_fin α with ⟨n, ⟨e⟩⟩
  exact ⟨.ofEquiv _ e.symm⟩
