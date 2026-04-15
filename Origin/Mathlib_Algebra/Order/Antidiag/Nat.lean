/-
Extracted from Algebra/Order/Antidiag/Nat.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Sets of tuples with a fixed product

This file defines the finite set of `d`-tuples of natural numbers with a fixed product `n` as
`Nat.finMulAntidiag`.

## Main Results
* There are `d^(ω n)` ways to write `n` as a product of `d` natural numbers, when `n` is squarefree
  (`card_finMulAntidiag_of_squarefree`)
* There are `3^(ω n)` pairs of natural numbers whose `lcm` is `n`, when `n` is squarefree
  (`card_pair_lcm_eq`)
-/

open Finset

open scoped ArithmeticFunction

namespace PNat

-- INSTANCE (free from Core): instHasAntidiagonal

This is `Nat.divisorsAntidiagonal` without a special case for `n = 0`. -/

  let divisorsAntidiagonal (n : ℕ+) : Finset (ℕ+ × ℕ+) :=

    (Nat.divisorsAntidiagonal n).attach.map

      ⟨fun x =>

        (⟨x.val.1, Nat.pos_of_mem_divisors <| Nat.fst_mem_divisors_of_mem_antidiagonal x.prop⟩,

        ⟨x.val.2, Nat.pos_of_mem_divisors <| Nat.snd_mem_divisors_of_mem_antidiagonal x.prop⟩),

      fun _ _ h => Subtype.ext <| Prod.ext (congr_arg (·.1.val) h) (congr_arg (·.2.val) h)⟩

  have mem_divisorsAntidiagonal {n : ℕ+} (x : ℕ+ × ℕ+) :

    x ∈ divisorsAntidiagonal n ↔ x.1 * x.2 = n := by

    simp_rw [divisorsAntidiagonal, Finset.mem_map, Finset.mem_attach, Function.Embedding.coeFn_mk,

      Prod.ext_iff, true_and, ← coe_inj, Subtype.exists]

    simp

  { antidiagonal := fun n ↦ divisorsAntidiagonal (Additive.toMul n) |>.map

      (.prodMap (Additive.ofMul.toEmbedding) (Additive.ofMul.toEmbedding))

    mem_antidiagonal := by simp [← ofMul_mul, mem_divisorsAntidiagonal] }

end PNat

namespace Nat

def finMulAntidiag (d : ℕ) (n : ℕ) : Finset (Fin d → ℕ) :=
  if hn : 0 < n then
    (Finset.finAntidiagonal d (Additive.ofMul (α := ℕ+) ⟨n, hn⟩)).map <|
      .arrowCongrRight <| Additive.toMul.toEmbedding.trans <| ⟨PNat.val, PNat.coe_injective⟩
  else
    ∅
