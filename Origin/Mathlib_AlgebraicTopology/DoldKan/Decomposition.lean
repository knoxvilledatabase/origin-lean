/-
Extracted from AlgebraicTopology/DoldKan/Decomposition.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Decomposition of the Q endomorphisms

In this file, we obtain a lemma `decomposition_Q` which expresses
explicitly the projection `(Q q).f (n+1) : X _⦋n+1⦌ ⟶ X _⦋n+1⦌`
(`X : SimplicialObject C` with `C` a preadditive category) as
a sum of terms which are postcompositions with degeneracies.

(TODO @joelriou: when `C` is abelian, define the degenerate
subcomplex of the alternating face map complex of `X` and show
that it is a complement to the normalized Moore complex.)

Then, we introduce an ad hoc structure `MorphComponents X n Z` which
can be used in order to define morphisms `X _⦋n+1⦌ ⟶ Z` using the
decomposition provided by `decomposition_Q`. This shall play a critical
role in the proof that the functor
`N₁ : SimplicialObject C ⥤ Karoubi (ChainComplex C ℕ))`
reflects isomorphisms.

(See `Equivalence.lean` for the general strategy of proof of the Dold-Kan equivalence.)

-/

open CategoryTheory CategoryTheory.Category CategoryTheory.Preadditive

  Opposite Simplicial

noncomputable section

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type*} [Category* C] [Preadditive C] {X X' : SimplicialObject C}

set_option backward.isDefEq.respectTransparency false in

theorem decomposition_Q (n q : ℕ) :
    ((Q q).f (n + 1) : X _⦋n + 1⦌ ⟶ X _⦋n + 1⦌) =
      ∑ i : Fin (n + 1) with i.val < q, (P i).f (n + 1) ≫ X.δ i.rev.succ ≫ X.σ (Fin.rev i) := by
  induction q with
  | zero =>
    simp only [Q_zero, HomologicalComplex.zero_f_apply, Nat.not_lt_zero,
      Finset.filter_false, Finset.sum_empty]
  | succ q hq =>
    by_cases! hqn : n < q
    · rw [Q_is_eventually_constant (show n + 1 ≤ q by lia), hq]
      congr 1
      ext ⟨x, hx⟩
      simp_rw [Finset.mem_filter_univ]
      lia
    · obtain ⟨a, ha⟩ := Nat.le.dest hqn
      rw [Q_succ, HomologicalComplex.sub_f_apply, HomologicalComplex.comp_f, hq]
      symm
      conv_rhs => rw [sub_eq_add_neg, add_comm]
      let q' : Fin (n + 1) := ⟨q, Nat.lt_succ_of_le hqn⟩
      rw [← @Finset.add_sum_erase _ _ _ _ _ _ q' (by simp [q'])]
      congr
      · have hnaq' : n = a + q := by lia
        simp only [(HigherFacesVanish.of_P q n).comp_Hσ_eq hnaq', q'.rev_eq hnaq', neg_neg]
        rfl
      · ext ⟨i, hi⟩
        simp_rw [Finset.mem_erase, Finset.mem_filter_univ, q', ne_eq, Fin.mk.injEq]
        lia

variable (X)
