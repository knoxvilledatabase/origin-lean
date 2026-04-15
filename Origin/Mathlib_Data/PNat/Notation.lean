/-
Extracted from Data/PNat/Notation.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Definition and notation for positive natural numbers -/

def PNat := { n : ℕ // 0 < n } deriving DecidableEq
