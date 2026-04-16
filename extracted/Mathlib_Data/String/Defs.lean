/-
Extracted from Data/String/Defs.lean
Genuine: 7 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Init

noncomputable section

/-!
# Definitions for `String`

This file defines a bunch of functions for the `String` datatype.
-/

namespace String

def leftpad (n : Nat) (c : Char := ' ') (s : String) : String :=
  ⟨List.leftpad n c s.data⟩

def replicate (n : Nat) (c : Char) : String :=
  ⟨List.replicate n c⟩

def rightpad (n : Nat) (c : Char := ' ') (s : String) : String :=
  s ++ String.replicate (n - s.length) c

def IsPrefix : String → String → Prop
  | ⟨d1⟩, ⟨d2⟩ => List.IsPrefix d1 d2

def IsSuffix : String → String → Prop
  | ⟨d1⟩, ⟨d2⟩ => List.IsSuffix d1 d2

def mapTokens (c : Char) (f : String → String) : String → String :=
  intercalate (singleton c) ∘ List.map f ∘ (·.split (· = c))

def head (s : String) : Char :=
  s.iter.curr

end String
