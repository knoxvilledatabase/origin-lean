/-
Extracted from AlgebraicTopology/DoldKan/NCompGamma.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! The unit isomorphism of the Dold-Kan equivalence

In order to construct the unit isomorphism of the Dold-Kan equivalence,
we first construct natural transformations
`Γ₂N₁.natTrans : N₁ ⋙ Γ₂ ⟶ toKaroubi (SimplicialObject C)` and
`Γ₂N₂.natTrans : N₂ ⋙ Γ₂ ⟶ 𝟭 (SimplicialObject C)`.
It is then shown that `Γ₂N₂.natTrans` is an isomorphism by using
that it becomes an isomorphism after the application of the functor
`N₂ : Karoubi (SimplicialObject C) ⥤ Karoubi (ChainComplex C ℕ)`
which reflects isomorphisms.

(See `Equivalence.lean` for the general strategy of proof of the Dold-Kan equivalence.)

-/

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Idempotents

  SimplexCategory Opposite SimplicialObject Simplicial DoldKan

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type*} [Category* C] [Preadditive C]

theorem PInfty_comp_map_mono_eq_zero (X : SimplicialObject C) {n : ℕ} {Δ' : SimplexCategory}
    (i : Δ' ⟶ ⦋n⦌) [hi : Mono i] (h₁ : Δ'.len ≠ n) (h₂ : ¬Isδ₀ i) :
    PInfty.f n ≫ X.map i.op = 0 := by
  induction Δ' using SimplexCategory.rec with | _ m
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt (len_lt_of_mono i fun h => by
        rw [← h] at h₁
        exact h₁ rfl)
  rcases k with _ | k
  · change n = m + 1 at hk
    subst hk
    obtain ⟨j, rfl⟩ := eq_δ_of_mono i
    rw [Isδ₀.iff] at h₂
    have h₃ : 1 ≤ (j : ℕ) := by
      by_contra h
      exact h₂ (by simpa only [Fin.ext_iff, not_le, Nat.lt_one_iff] using h)
    exact (HigherFacesVanish.of_P (m + 1) m).comp_δ_eq_zero j h₂ (by lia)
  · simp only [← add_assoc] at hk
    clear h₂ hi
    subst hk
    obtain ⟨j₁ : Fin (_ + 1), i, rfl⟩ :=
      eq_comp_δ_of_not_surjective i fun h => by
        rw [← SimplexCategory.epi_iff_surjective] at h
        grind [→ le_of_epi]
    obtain ⟨j₂, i, rfl⟩ :=
      eq_comp_δ_of_not_surjective i fun h => by
        rw [← SimplexCategory.epi_iff_surjective] at h
        grind [→ le_of_epi]
    by_cases hj₁ : j₁ = 0
    · subst hj₁
      rw [assoc, ← SimplexCategory.δ_comp_δ'' (Fin.zero_le _)]
      simp only [op_comp, X.map_comp, assoc, PInfty_f]
      erw [(HigherFacesVanish.of_P _ _).comp_δ_eq_zero_assoc _ j₂.succ_ne_zero, zero_comp]
      simp only [Fin.succ]
      lia
    · simp only [op_comp, X.map_comp, assoc, PInfty_f]
      erw [(HigherFacesVanish.of_P _ _).comp_δ_eq_zero_assoc _ hj₁, zero_comp]
      by_contra
      exact hj₁ (by simp only [Fin.ext_iff, Fin.val_zero]; lia)

set_option backward.isDefEq.respectTransparency false in
