/-
Extracted from Algebra/Order/Module/Equiv.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Linear equivalence for order type synonyms
-/

variable (α β : Type*)

variable [Semiring α] [AddCommMonoid β] [Module α β]

def toLexLinearEquiv : β ≃ₗ[α] Lex β := (toLexAddEquiv β).toLinearEquiv toLex_smul

def ofLexLinearEquiv : Lex β ≃ₗ[α] β := (ofLexAddEquiv β).toLinearEquiv ofLex_smul
