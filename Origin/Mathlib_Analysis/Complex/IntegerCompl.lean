/-
Extracted from Analysis/Complex/IntegerCompl.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Integer Complement

We define the complement of the integers in the complex plane and give some basic lemmas about it.
We also show that the upper half plane embeds into the integer complement.

-/

open UpperHalfPlane

def Complex.integerComplement := (Set.range ((↑) : ℤ → ℂ))ᶜ

namespace Complex

local notation "ℂ_ℤ" => integerComplement
