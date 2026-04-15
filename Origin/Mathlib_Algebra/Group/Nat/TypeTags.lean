/-
Extracted from Algebra/Group/Nat/TypeTags.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lemmas about `Multiplicative ℕ`
-/

assert_not_exists MonoidWithZero DenselyOrdered

open Multiplicative

namespace Nat

lemma toAdd_pow (a : Multiplicative ℕ) (b : ℕ) : (a ^ b).toAdd = a.toAdd * b := mul_comm _ _
