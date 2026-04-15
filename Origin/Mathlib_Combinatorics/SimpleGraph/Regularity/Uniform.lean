/-
Extracted from Combinatorics/SimpleGraph/Regularity/Uniform.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Graph uniformity and uniform partitions

In this file we define uniformity of a pair of vertices in a graph and uniformity of a partition of
vertices of a graph. Both are also known as ε-regularity.

Finsets of vertices `s` and `t` are `ε`-uniform in a graph `G` if their edge density is at most
`ε`-far from the density of any big enough `s'` and `t'` where `s' ⊆ s`, `t' ⊆ t`.
The definition is pretty technical, but it amounts to the edges between `s` and `t` being "random"
The literature contains several definitions which are equivalent up to scaling `ε` by some constant
when the partition is equitable.

A partition `P` of the vertices is `ε`-uniform if the proportion of `ε`-uniform pairs of parts is
greater than `(1 - ε)`.

## Main declarations

* `SimpleGraph.IsUniform`: Graph uniformity of a pair of finsets of vertices.
* `SimpleGraph.nonuniformWitness`: `G.nonuniformWitness ε s t` and `G.nonuniformWitness ε t s`
  together witness the non-uniformity of `s` and `t`.
* `Finpartition.nonUniforms`: Nonuniform pairs of parts of a partition.
* `Finpartition.IsUniform`: Uniformity of a partition.
* `Finpartition.nonuniformWitnesses`: For each non-uniform pair of parts of a partition, pick
  witnesses of non-uniformity and dump them all together.

## References

[Yaël Dillies, Bhavik Mehta, *Formalising Szemerédi’s Regularity Lemma in Lean*][srl_itp]
-/

open Finset

variable {α 𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-! ### Graph uniformity -/

namespace SimpleGraph

variable (G : SimpleGraph α) [DecidableRel G.Adj] (ε : 𝕜) {s t : Finset α} {a b : α}

def IsUniform (s t : Finset α) : Prop :=
  ∀ ⦃s'⦄, s' ⊆ s → ∀ ⦃t'⦄, t' ⊆ t → (#s : 𝕜) * ε ≤ #s' →
    (#t : 𝕜) * ε ≤ #t' → |(G.edgeDensity s' t' : 𝕜) - (G.edgeDensity s t : 𝕜)| < ε

deriving Decidable

variable {G ε}

theorem IsUniform.mono {ε' : 𝕜} (h : ε ≤ ε') (hε : IsUniform G ε s t) : IsUniform G ε' s t :=
  fun s' hs' t' ht' hs ht => by
  refine (hε hs' ht' (le_trans ?_ hs) (le_trans ?_ ht)).trans_le h <;> gcongr

omit [IsStrictOrderedRing 𝕜] in

theorem IsUniform.symm : Symmetric (IsUniform G ε) := fun s t h t' ht' s' hs' ht hs => by
  rw [edgeDensity_comm _ t', edgeDensity_comm _ t]
  exact h hs' ht' hs ht

variable (G)

omit [IsStrictOrderedRing 𝕜] in

theorem isUniform_comm : IsUniform G ε s t ↔ IsUniform G ε t s :=
  ⟨fun h => h.symm, fun h => h.symm⟩

lemma isUniform_one : G.IsUniform (1 : 𝕜) s t := by
  intro s' hs' t' ht' hs ht
  rw [mul_one] at hs ht
  rw [eq_of_subset_of_card_le hs' (Nat.cast_le.1 hs),
    eq_of_subset_of_card_le ht' (Nat.cast_le.1 ht), sub_self, abs_zero]
  exact zero_lt_one

variable {G}

lemma IsUniform.pos (hG : G.IsUniform ε s t) : 0 < ε :=
  not_le.1 fun hε ↦ (hε.trans <| abs_nonneg _).not_gt <| hG (empty_subset _) (empty_subset _)
    (by simpa using mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hε)
    (by simpa using mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hε)
