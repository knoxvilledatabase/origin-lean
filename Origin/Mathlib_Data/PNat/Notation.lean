/-
Extracted from Data/PNat/Notation.lean
Genuine: 2 | Conflates: 0 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.Data.Nat.Notation

noncomputable section

/-! # Definition and notation for positive natural numbers -/

def PNat := { n : ℕ // 0 < n } deriving DecidableEq

notation "ℕ+" => PNat

@[coe]
def PNat.val : ℕ+ → ℕ := Subtype.val

instance coePNatNat : Coe ℕ+ ℕ :=
  ⟨PNat.val⟩

instance : Repr ℕ+ :=
  ⟨fun n n' => reprPrec n.1 n'⟩
