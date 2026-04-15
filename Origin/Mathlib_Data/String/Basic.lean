/-
Extracted from Data/String/Basic.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Strings

Supplementary theorems about the `String` type.
-/

namespace String

def ltb (s₁ s₂ : Legacy.Iterator) : Bool :=
  if s₂.hasNext then
    if s₁.hasNext then
      if s₁.curr = s₂.curr then
        ltb s₁.next s₂.next
      else s₁.curr < s₂.curr
    else true
  else false

-- INSTANCE (free from Core): LT'

-- INSTANCE (free from Core): decidableLT'
