/-
Extracted from Combinatorics/Colex.lean
Genuine: 7 of 13 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core

/-!
# Colexicographic order

We define the colex order for finite sets, and give a couple of important lemmas and properties
relating to it.

The colex ordering likes to avoid large values: If the biggest element of `t` is bigger than all
elements of `s`, then `s < t`.

In the special case of `ℕ`, it can be thought of as the "binary" ordering. That is, order `s` based
on $∑_{i ∈ s} 2^i$. It's defined here on `Finset α` for any linear order `α`.

In the context of the Kruskal-Katona theorem, we are interested in how colex behaves for sets of a
fixed size. For example, for size 3, the colex order on ℕ starts
`012, 013, 023, 123, 014, 024, 124, 034, 134, 234, ...`

## Main statements

* Colex order properties - linearity, decidability and so on.
* `Finset.Colex.forall_lt_mono`: if `s < t` in colex, and everything in `t` is `< a`, then
  everything in `s` is `< a`. This confirms the idea that an enumeration under colex will exhaust
  all sets using elements `< a` before allowing `a` to be included.
* `Finset.toColex_image_le_toColex_image`: Strictly monotone functions preserve colex.
* `Finset.geomSum_le_geomSum_iff_toColex_le_toColex`: Colex for α = ℕ is the same as binary.
  This also proves binary expansions are unique.

## See also

Related files are:
* `Data.List.Lex`: Lexicographic order on lists.
* `Data.Pi.Lex`: Lexicographic order on `Πₗ i, α i`.
* `Data.PSigma.Order`: Lexicographic order on `Σ' i, α i`.
* `Data.Sigma.Order`: Lexicographic order on `Σ i, α i`.
* `Data.Prod.Lex`: Lexicographic order on `α × β`.

## TODO

* Generalise `Colex.initSeg` so that it applies to `ℕ`.

## References

* https://github.com/b-mehta/maths-notes/blob/master/iii/mich/combinatorics.pdf

## Tags

colex, colexicographic, binary
-/

open Function

variable {α β : Type*}

namespace Finset

open Colex

-- INSTANCE (free from Core): :

namespace Colex

section PartialOrder

variable [PartialOrder α] [PartialOrder β] {f : α → β} {𝒜 𝒜₁ 𝒜₂ : Finset (Finset α)}
  {s t u : Finset α} {a b : α}

-- INSTANCE (free from Core): instLE

private lemma trans_aux (hst : toColex s ≤ toColex t) (htu : toColex t ≤ toColex u)
    (has : a ∈ s) (hat : a ∉ t) : ∃ b, b ∈ u ∧ b ∉ s ∧ a ≤ b := by
  classical
  let s' : Finset α := {b ∈ s | b ∉ t ∧ a ≤ b}
  have ⟨b, hb, hbmax⟩ := s'.exists_maximal ⟨a, by simp [s', has, hat]⟩
  simp only [s', mem_filter, and_imp] at hb hbmax
  have ⟨c, hct, hcs, hbc⟩ := hst hb.1 hb.2.1
  by_cases hcu : c ∈ u
  · exact ⟨c, hcu, hcs, hb.2.2.trans hbc⟩
  have ⟨d, hdu, hdt, hcd⟩ := htu hct hcu
  have had : a ≤ d := hb.2.2.trans <| hbc.trans hcd
  refine ⟨d, hdu, fun hds ↦ not_lt_iff_le_imp_ge.2 (hbmax hds hdt had) ?_, had⟩
  exact hbc.trans_lt <| hcd.lt_of_ne <| ne_of_mem_of_not_mem hct hdt

set_option backward.privateInPublic true in

private lemma antisymm_aux (hst : toColex s ≤ toColex t) (hts : toColex t ≤ toColex s) : s ⊆ t := by
  intro a has
  by_contra hat
  have ⟨_b, hb₁, hb₂, _⟩ := trans_aux hst hts has hat
  exact hb₂ hb₁

set_option backward.privateInPublic true in

set_option backward.privateInPublic.warn false in

-- INSTANCE (free from Core): instPartialOrder

lemma toColex_lt_toColex :
    toColex s < toColex t ↔ s ≠ t ∧ ∀ ⦃a⦄, a ∈ s → a ∉ t → ∃ b, b ∈ t ∧ b ∉ s ∧ a ≤ b := by
  simp [lt_iff_le_and_ne, toColex_le_toColex, and_comm]

lemma toColex_mono : Monotone (@toColex (Finset α)) :=
  fun _s _t hst _a has hat ↦ (hat <| hst has).elim

lemma toColex_strictMono : StrictMono (@toColex (Finset α)) :=
  toColex_mono.strictMono_of_injective toColex.injective

lemma toColex_le_toColex_of_subset (h : s ⊆ t) : toColex s ≤ toColex t := toColex_mono h

lemma toColex_lt_toColex_of_ssubset (h : s ⊂ t) : toColex s < toColex t := toColex_strictMono h

-- INSTANCE (free from Core): instOrderBot
