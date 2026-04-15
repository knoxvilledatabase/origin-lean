/-
Extracted from Algebra/Order/Antidiag/Pi.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Antidiagonal of functions as finsets

This file provides the finset of functions summing to a specific value on a finset. Such finsets
should be thought of as the "antidiagonals" in the space of functions.

Precisely, for a commutative monoid `μ` with antidiagonals (see `Finset.HasAntidiagonal`),
`Finset.piAntidiag s n` is the finset of all functions `f : ι → μ` with support contained in `s` and
such that the sum of its values equals `n : μ`.

We define it recursively on `s` using `Finset.HasAntidiagonal.antidiagonal : μ → Finset (μ × μ)`.
Technically, we non-canonically identify `s` with `Fin n` where `n = s.card`, recurse on `n` using
that `(Fin (n + 1) → μ) ≃ (Fin n → μ) × μ`, and show the end result doesn't depend on our
identification. See `Finset.finAntidiag` for the details.

## Main declarations

* `Finset.piAntidiag s n`: Finset of all functions `f : ι → μ` with support contained in `s` and
  such that the sum of its values equals `n : μ`.
* `Finset.finAntidiagonal d n`: Computationally efficient special case of `Finset.piAntidiag` when
  `ι := Fin d`.

## TODO

`Finset.finAntidiagonal` is strictly more general than `Finset.Nat.antidiagonalTuple`. Deduplicate.

## See also

`Finset.finsuppAntidiag` for the `Finset (ι →₀ μ)`-valued version of `Finset.piAntidiag`.
-/

open Function

variable {ι μ μ' : Type*}

namespace Finset

section AddCommMonoid

variable [DecidableEq ι] [AddCommMonoid μ] [HasAntidiagonal μ] [DecidableEq μ] {n : μ}

/-!
### `Fin d → μ`

In this section, we define the antidiagonals in `Fin d → μ` by recursion on `d`. Note that this is
computationally efficient, although probably not as efficient as `Finset.Nat.antidiagonalTuple`.
-/

set_option backward.proofsInPublic true in

def finAntidiagonal (d : ℕ) (n : μ) : Finset (Fin d → μ) :=
  aux d n
where
  /-- Auxiliary construction for `finAntidiagonal` that bundles a proof of lawfulness
  (`mem_finAntidiagonal`), as this is needed to invoke `disjiUnion`. Using `Finset.disjiUnion` makes
  this computationally much more efficient than using `Finset.biUnion`. -/
  aux (d : ℕ) (n : μ) : {s : Finset (Fin d → μ) // ∀ f, f ∈ s ↔ ∑ i, f i = n} :=
    match d with
    | 0 =>
      if h : n = 0 then
        ⟨{0}, by simp [h, Subsingleton.elim _ ![]]⟩
      else
        ⟨∅, by simp [Ne.symm h]⟩
    | d + 1 =>
      { val := (antidiagonal n).disjiUnion
          (fun ab => (aux d ab.2).1.map {
              toFun := Fin.cons (ab.1)
              inj' := Fin.cons_right_injective _ })
          (fun i _hi j _hj hij => Finset.disjoint_left.2 fun t hti htj => hij <| by
            simp_rw [Finset.mem_map, Embedding.coeFn_mk] at hti htj
            obtain ⟨ai, hai, hij'⟩ := hti
            obtain ⟨aj, haj, rfl⟩ := htj
            rw [Fin.cons_inj] at hij'
            ext
            · exact hij'.1
            · obtain ⟨-, rfl⟩ := hij'
              rw [← (aux d i.2).prop ai |>.mp hai, ← (aux d j.2).prop ai |>.mp haj])
        property := fun f => by
          simp_rw [mem_disjiUnion, mem_antidiagonal, mem_map, Embedding.coeFn_mk, Prod.exists,
            (aux d _).prop, Fin.sum_univ_succ]
          constructor
          · rintro ⟨a, b, rfl, g, rfl, rfl⟩
            simp only [Fin.cons_zero, Fin.cons_succ]
          · intro hf
            exact ⟨_, _, hf, _, rfl, Fin.cons_self_tail f⟩ }
