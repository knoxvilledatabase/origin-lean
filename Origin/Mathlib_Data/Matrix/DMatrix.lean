/-
Extracted from Data/Matrix/DMatrix.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Dependent-typed matrices
-/

universe u u' v w z

def DMatrix (m : Type u) (n : Type u') (α : m → n → Type v) : Type max u u' v :=
  ∀ i j, α i j

variable {m n : Type*}

variable {α : m → n → Type v}

namespace DMatrix

section Ext

variable {M N : DMatrix m n α}

theorem ext_iff : (∀ i j, M i j = N i j) ↔ M = N :=
  ⟨fun h => funext fun i => funext <| h i, fun h => by simp [h]⟩
