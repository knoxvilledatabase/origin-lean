/-
Extracted from AlgebraicTopology/SimplicialSet/AnodyneExtensions/Rank.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Rank functions for pairings

We introduce types of (weak) rank functions for a pairing `P`
of a subcomplex `A` of a simplicial set `X`. These are
functions `f : P.II → α` such that `P.AncestralRel x y` implies `f x < f y`
(in the weak case, we require this only under the additional condition
that `x` and `y` are of the same dimension). Such rank functions
are used in order to show that the ancestrality relation on `P.II` is well founded,
i.e. that `P` is regular (when we already know `P` is proper).
Conversely, we shall show that if `P` is regular,
then `P.RankFunction ℕ` is non empty (TODO @joelriou).

(We also introduce similar definitions for the structure `PairingCore`.)


## References
* [Sean Moss, *Another approach to the Kan-Quillen model structure*][moss-2020]

-/

universe v u

open CategoryTheory Simplicial

namespace SSet.Subcomplex

variable {X : SSet.{u}} {A : X.Subcomplex}

namespace Pairing

variable {X : SSet.{u}} {A : X.Subcomplex} (P : A.Pairing)
  (α : Type v) [PartialOrder α]

structure RankFunction where
  /-- the rank function -/
  rank : P.II → α
  lt {x y : P.II} : P.AncestralRel x y → rank x < rank y

namespace RankFunction

variable {P α} [WellFoundedLT α] (f : P.RankFunction α)

include f

lemma wf_ancestralRel : WellFounded P.AncestralRel := by
  rw [wellFounded_iff_isEmpty_descending_chain]
  exact ⟨fun ⟨g, hg⟩ ↦ not_strictAnti_of_wellFoundedLT (f.rank ∘ g)
    (strictAnti_nat_of_succ_lt (fun n ↦ f.lt (hg n)))⟩

lemma isRegular [P.IsProper] : P.IsRegular where
  wf := f.wf_ancestralRel

end RankFunction

structure WeakRankFunction where
  /-- the (weak) rank function -/
  rank : P.II → α
  lt {x y : P.II} : P.AncestralRel x y → x.1.dim = y.1.dim → rank x < rank y

namespace WeakRankFunction

variable {P α} [WellFoundedLT α] [P.IsProper] (f : P.WeakRankFunction α)

include f

lemma wf_ancestralRel : WellFounded P.AncestralRel := by
  rw [wellFounded_iff_isEmpty_descending_chain]
  refine ⟨fun ⟨g, hg⟩ ↦ ?_⟩
  obtain ⟨n₀, hn₀⟩ :=
    (wellFoundedGT_iff_monotone_chain_condition (α := ℕᵒᵈ)).1
      inferInstance ⟨fun n ↦ (g n).1.dim,
        monotone_nat_of_le_succ (fun n ↦ (hg n).dim_le)⟩
  dsimp at hn₀
  refine not_strictAnti_of_wellFoundedLT (fun n ↦ f.rank (g (n₀ + n)))
    (strictAnti_nat_of_succ_lt (fun n ↦ ?_))
  rw [← add_assoc]
  exact f.lt (hg _) (by rw [← hn₀ (n₀ + n + 1) (by lia), ← hn₀ (n₀ + n) (by lia)])

lemma isRegular : P.IsRegular where
  wf := f.wf_ancestralRel

end WeakRankFunction
