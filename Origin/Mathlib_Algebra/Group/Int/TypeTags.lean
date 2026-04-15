/-
Extracted from Algebra/Group/Int/TypeTags.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lemmas about `Multiplicative ℤ`.
-/

open Nat

namespace Int

section Multiplicative

open Multiplicative

lemma toAdd_pow (a : Multiplicative ℤ) (b : ℕ) : (a ^ b).toAdd = a.toAdd * b := mul_comm _ _

lemma toAdd_zpow (a : Multiplicative ℤ) (b : ℤ) : (a ^ b).toAdd = a.toAdd * b := mul_comm _ _
