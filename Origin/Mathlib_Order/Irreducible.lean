/-
Extracted from Order/Irreducible.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Irreducible and prime elements in an order

This file defines irreducible and prime elements in an order and shows that in a well-founded
lattice every element decomposes as a supremum of irreducible elements.

An element is sup-irreducible (resp. inf-irreducible) if it isn't `⊥` and can't be written as the
supremum of any strictly smaller elements. An element is sup-prime (resp. inf-prime) if it isn't `⊥`
and is greater than the supremum of any two elements less than it.

Primality implies irreducibility in general. The converse only holds in distributive lattices.
Both hold for all (non-minimal) elements in a linear order.

## Main declarations

* `SupIrred a`: Sup-irreducibility, `a` isn't minimal and `a = b ⊔ c → a = b ∨ a = c`
* `InfIrred a`: Inf-irreducibility, `a` isn't maximal and `a = b ⊓ c → a = b ∨ a = c`
* `SupPrime a`: Sup-primality, `a` isn't minimal and `a ≤ b ⊔ c → a ≤ b ∨ a ≤ c`
* `InfIrred a`: Inf-primality, `a` isn't maximal and `a ≥ b ⊓ c → a ≥ b ∨ a ≥ c`
* `exists_supIrred_decomposition`/`exists_infIrred_decomposition`: Decomposition into irreducibles
  in a well-founded semilattice.
-/

open Finset OrderDual

variable {ι α : Type*}

/-! ### Irreducible and prime elements -/

section SemilatticeSup

variable [SemilatticeSup α] {a b c : α}

def SupIrred (a : α) : Prop :=
  ¬IsMin a ∧ ∀ ⦃b c⦄, b ⊔ c = a → b = a ∨ c = a

def SupPrime (a : α) : Prop :=
  ¬IsMin a ∧ ∀ ⦃b c⦄, a ≤ b ⊔ c → a ≤ b ∨ a ≤ c

theorem SupIrred.not_isMin (ha : SupIrred a) : ¬IsMin a :=
  ha.1

theorem SupPrime.not_isMin (ha : SupPrime a) : ¬IsMin a :=
  ha.1

theorem IsMin.not_supIrred (ha : IsMin a) : ¬SupIrred a := fun h => h.1 ha

theorem IsMin.not_supPrime (ha : IsMin a) : ¬SupPrime a := fun h => h.1 ha
