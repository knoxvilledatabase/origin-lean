/-
Extracted from Data/String/Defs.lean
Genuine: 8 of 8 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Definitions for `String`

This file defines a bunch of functions for the `String` datatype.
-/

def Char.isAscii (c : Char) : Bool := c.toNat < 0x80

namespace String

def leftpad (n : Nat) (c : Char := ' ') (s : String) : String :=
  ofList (List.leftpad n c s.toList)

def replicate (n : Nat) (c : Char) : String :=
  ofList (List.replicate n c)

def rightpad (n : Nat) (c : Char := ' ') (s : String) : String :=
  s ++ String.replicate (n - s.length) c

def IsPrefix : String → String → Prop
  | d1, d2 => List.IsPrefix d1.toList d2.toList

def IsSuffix : String → String → Prop
  | d1, d2 => List.IsSuffix d1.toList d2.toList

def mapTokens (c : Char) (f : String → String) : String → String :=
  intercalate (singleton c) ∘ List.map f ∘ (·.splitToList (· = c))

def head (s : String) : Char :=
  s.front

end String
