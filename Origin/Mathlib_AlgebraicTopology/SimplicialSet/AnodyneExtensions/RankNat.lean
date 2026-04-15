/-
Extracted from AlgebraicTopology/SimplicialSet/AnodyneExtensions/RankNat.lean
Genuine: 8 of 11 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Existence of a rank function to natural numbers

In this file, we show that if `P : A.Pairing` is
a regular pairing of subcomplex `A` of a simplicial set `X`,
then there exists a rank function for `P` with values in `ℕ`.

-/

universe u

open Simplicial

namespace SSet.Subcomplex.Pairing

variable {X : SSet.{u}} {A : X.Subcomplex} (P : A.Pairing)

-- INSTANCE (free from Core): (y

variable {y : P.II} (hy : Acc P.AncestralRel y)

noncomputable def rank' : ℕ :=
  Acc.recOn hy (fun y _ r ↦ ⨆ (x : { x // P.AncestralRel x y }), r x x.2 + 1)

lemma rank'_eq :
    P.rank' hy = ⨆ (x : { x // P.AncestralRel x y }), P.rank' (hy.inv x.2) + 1 := by
  change P.rank' (Acc.intro y fun _ => hy.inv) = _
  rfl

lemma rank'_lt {x : P.II} (r : P.AncestralRel x y) :
    P.rank' (hy.inv r) < P.rank' hy := by
  rw [P.rank'_eq hy, ← Nat.add_one_le_iff]
  exact le_csSup (Finite.bddAbove_range _) ⟨⟨x, r⟩, rfl⟩

end

section IsRegular

variable [P.IsRegular]

noncomputable def rank (x : P.II) : ℕ :=
  P.rank' (P.wf.apply x)

variable {P} in

lemma rank_lt {x y : P.II} (h : P.AncestralRel x y) :
    P.rank x < P.rank y :=
  P.rank'_lt _ h

noncomputable def rankFunction : P.RankFunction ℕ where
  rank := P.rank
  lt := P.rank_lt

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

end IsRegular

lemma isRegular_iff_nonempty_rankFunction [P.IsProper] :
    P.IsRegular ↔ Nonempty (P.RankFunction ℕ) :=
  ⟨fun _ ↦ inferInstance, fun ⟨h⟩ ↦ h.isRegular⟩

lemma isRegular_iff_nonempty_weakRankFunction [P.IsProper] :
    P.IsRegular ↔ Nonempty (P.WeakRankFunction ℕ) :=
  ⟨fun _ ↦ inferInstance, fun ⟨h⟩ ↦ h.isRegular⟩

end SSet.Subcomplex.Pairing
