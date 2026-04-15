/-
Extracted from RingTheory/UniqueFactorizationDomain/FactorSet.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Set of factors

## Main definitions
* `Associates.FactorSet`: multiset of factors of an element, unique up to propositional equality.
* `Associates.factors`: determine the `FactorSet` for a given element.

## TODO
* set up the complete lattice structure on `FactorSet`.

-/

variable {α : Type*}

local infixl:50 " ~ᵤ " => Associated

namespace Associates

open UniqueFactorizationMonoid Associated Multiset

variable [CommMonoidWithZero α]

abbrev FactorSet.{u} (α : Type u) [CommMonoidWithZero α] : Type u :=
  WithTop (Multiset { a : Associates α // Irreducible a })

attribute [local instance] Associated.setoid

theorem FactorSet.coe_add {a b : Multiset { a : Associates α // Irreducible a }} :
    (↑(a + b) : FactorSet α) = a + b := by norm_cast

theorem FactorSet.sup_add_inf_eq_add [DecidableEq (Associates α)] :
    ∀ a b : FactorSet α, a ⊔ b + a ⊓ b = a + b
  | ⊤, b => show ⊤ ⊔ b + ⊤ ⊓ b = ⊤ + b by simp
  | a, ⊤ => show a ⊔ ⊤ + a ⊓ ⊤ = a + ⊤ by simp
  | WithTop.some a, WithTop.some b =>
    show (a : FactorSet α) ⊔ b + (a : FactorSet α) ⊓ b = a + b by
      rw [← WithTop.coe_sup, ← WithTop.coe_inf, ← WithTop.coe_add, ← WithTop.coe_add,
        WithTop.coe_eq_coe]
      exact Multiset.union_add_inter _ _

def FactorSet.prod : FactorSet α → Associates α
  | ⊤ => 0
  | WithTop.some s => (s.map (↑)).prod
