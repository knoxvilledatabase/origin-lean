/-
Extracted from AlgebraicTopology/SimplexCategory/GeneratorsRelations/EpiMono.lean
Genuine: 14 of 19 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-! # Epi-mono factorization in the simplex category presented by generators and relations

This file aims to establish that there is a nice epi-mono factorization in `SimplexCategoryGenRel`.
More precisely, we introduce two morphism properties `P_δ` and `P_σ` that
single out morphisms that are compositions of `δ i` (resp. `σ i`).

The main result of this file is `exists_P_σ_P_δ_factorization`, which asserts that every
morphism as a decomposition of a `P_σ` followed by a `P_δ`.

-/

namespace SimplexCategoryGenRel

open CategoryTheory

section EpiMono

def splitMonoδ {n : ℕ} (i : Fin (n + 2)) : SplitMono (δ i) where
  retraction := by
    induction i using Fin.lastCases with
    | last => exact σ (Fin.last n)
    | cast i => exact σ i
  id := by
    cases i using Fin.lastCases
    · simp only [Fin.lastCases_last]
      exact δ_comp_σ_succ
    · simp only [Fin.lastCases_castSucc]
      exact δ_comp_σ_self

-- INSTANCE (free from Core): {n

def splitEpiσ {n : ℕ} (i : Fin (n + 1)) : SplitEpi (σ i) where
  section_ := δ i.castSucc
  id := δ_comp_σ_self

-- INSTANCE (free from Core): {n

abbrev P_σ := degeneracies.multiplicativeClosure

abbrev P_δ := faces.multiplicativeClosure

lemma P_σ.σ {n : ℕ} (i : Fin (n + 1)) : P_σ (σ i) := .of _ (.σ i)

lemma P_δ.δ {n : ℕ} (i : Fin (n + 2)) : P_δ (δ i) := .of _ (.δ i)

lemma isSplitEpi_P_σ {x y : SimplexCategoryGenRel} {e : x ⟶ y} (he : P_σ e) : IsSplitEpi e := by
  induction he with
  | of x hx => cases hx; infer_instance
  | id => infer_instance
  | comp_of _ _ _ h => cases h; infer_instance

lemma isSplitMono_P_δ {x y : SimplexCategoryGenRel} {m : x ⟶ y} (hm : P_δ m) :
    IsSplitMono m := by
  induction hm with
  | of x hx => cases hx; infer_instance
  | id => infer_instance
  | comp_of _ _ _ h => cases h; infer_instance

lemma isSplitEpi_toSimplexCategory_map_of_P_σ {x y : SimplexCategoryGenRel} {e : x ⟶ y}
    (he : P_σ e) : IsSplitEpi <| toSimplexCategory.map e := by
  constructor
  constructor
  apply SplitEpi.map
  exact isSplitEpi_P_σ he |>.exists_splitEpi.some

lemma isSplitMono_toSimplexCategory_map_of_P_δ {x y : SimplexCategoryGenRel} {m : x ⟶ y}
    (hm : P_δ m) : IsSplitMono <| toSimplexCategory.map m := by
  constructor
  constructor
  apply SplitMono.map
  exact isSplitMono_P_δ hm |>.exists_splitMono.some

lemma eq_or_len_le_of_P_δ {x y : SimplexCategoryGenRel} {f : x ⟶ y} (h_δ : P_δ f) :
    (∃ h : x = y, f = eqToHom h) ∨ x.len < y.len := by
  induction h_δ with
  | of _ hx => cases hx; right; simp
  | id => left; use rfl; simp
  | comp_of i u _ hg h' =>
    rcases h' with ⟨e, _⟩ | h' <;>
    apply Or.inr <;>
    cases hg
    · rw [e]
      exact Nat.lt_add_one _
    · exact Nat.lt_succ_of_lt h'

end EpiMono

section ExistenceOfFactorizations

private lemma switch_δ_σ₀ (i : Fin 1) (i' : Fin 2) :
    δ i' ≫ σ i = 𝟙 _ := by
  fin_cases i; fin_cases i'
  · exact δ_comp_σ_self
  · exact δ_comp_σ_succ

private lemma factor_δ_σ {n : ℕ} (i : Fin (n + 1)) (i' : Fin (n + 2)) :
    ∃ (z : SimplexCategoryGenRel) (e : mk n ⟶ z) (m : z ⟶ mk n)
      (_ : P_σ e) (_ : P_δ m), δ i' ≫ σ i = e ≫ m := by
  cases n with
  | zero => exact ⟨_, _, _, P_σ.id_mem _, P_δ.id_mem _, by simp [switch_δ_σ₀]⟩
  | succ n =>
    obtain h | ⟨j, j', h⟩ := switch_δ_σ i i'
    · exact ⟨_, _, _, P_σ.id_mem _, P_δ.id_mem _, by simp [h]⟩
    · exact ⟨_, _, _, P_σ.σ _, P_δ.δ _, h⟩

private lemma factor_P_δ_σ {n : ℕ} (i : Fin (n + 1)) {x : SimplexCategoryGenRel}
    (f : x ⟶ mk (n + 1)) (hf : P_δ f) : ∃ (z : SimplexCategoryGenRel) (e : x ⟶ z) (m : z ⟶ mk n)
      (_ : P_σ e) (_ : P_δ m), f ≫ σ i = e ≫ m := by
  induction n generalizing x with
  | zero => cases hf with
    | of _ h => cases h; exact factor_δ_σ _ _
    | id => exact ⟨_, _, _, P_σ.σ i, P_δ.id_mem _, by simp⟩
    | comp_of j f hf hg =>
      obtain ⟨k⟩ := hg
      obtain ⟨rfl, rfl⟩ | hf' := eq_or_len_le_of_P_δ hf
      · simpa using factor_δ_σ i k
      · simp at hf'
  | succ n hn =>
    cases hf with
    | of _ h => cases h; exact factor_δ_σ _ _
    | id n => exact ⟨_, _, _, P_σ.σ i, P_δ.id_mem _, by simp⟩
    | comp_of f g hf hg =>
      obtain ⟨k⟩ := hg
      obtain ⟨rfl, rfl⟩ | h' := eq_or_len_le_of_P_δ hf
      · simpa using factor_δ_σ i k
      · obtain h'' | ⟨j, j', h''⟩ := switch_δ_σ i k
        · exact ⟨_, _, _, P_σ.id_mem _, hf, by simp [h'']⟩
        · obtain ⟨z, e, m, he, hm, fac⟩ := hn j f hf
          exact ⟨z, e, m ≫ δ j', he, P_δ.comp_mem _ _ hm (P_δ.δ j'),
            by simp [h'', reassoc_of% fac]⟩

-- INSTANCE (free from Core): :

end ExistenceOfFactorizations

end SimplexCategoryGenRel
