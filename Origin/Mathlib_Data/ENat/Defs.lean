/-
Extracted from Data/ENat/Defs.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Definition and notation for extended natural numbers -/

def ENat : Type := WithTop ℕ deriving Top, Inhabited
