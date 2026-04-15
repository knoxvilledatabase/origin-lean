/-
Extracted from Combinatorics/Configuration.lean
Genuine: 16 of 24 | Dissolved: 0 | Infrastructure: 8
-/
import Origin.Core

/-!
# Configurations of Points and lines
This file introduces abstract configurations of points and lines, and proves some basic properties.

## Main definitions
* `Configuration.Nondegenerate`: Excludes certain degenerate configurations,
  and imposes uniqueness of intersection points.
* `Configuration.HasPoints`: A nondegenerate configuration in which
  every pair of lines has an intersection point.
* `Configuration.HasLines`:  A nondegenerate configuration in which
  every pair of points has a line through them.
* `Configuration.lineCount`: The number of lines through a given point.
* `Configuration.pointCount`: The number of lines through a given line.

## Main statements
* `Configuration.HasLines.card_le`: `HasLines` implies `|P| ≤ |L|`.
* `Configuration.HasPoints.card_le`: `HasPoints` implies `|L| ≤ |P|`.
* `Configuration.HasLines.hasPoints`: `HasLines` and `|P| = |L|` implies `HasPoints`.
* `Configuration.HasPoints.hasLines`: `HasPoints` and `|P| = |L|` implies `HasLines`.

Together, these four statements say that any two of the following properties imply the third:
(a) `HasLines`, (b) `HasPoints`, (c) `|P| = |L|`.

-/

open Finset

namespace Configuration

variable (P L : Type*) [Membership P L]

def Dual :=
  P

-- INSTANCE (free from Core): [h

-- INSTANCE (free from Core): [Finite

-- INSTANCE (free from Core): [h

set_option synthInstance.checkSynthOrder false in

-- INSTANCE (free from Core): :

class Nondegenerate : Prop where
  exists_point : ∀ l : L, ∃ p, p ∉ l
  exists_line : ∀ p, ∃ l : L, p ∉ l
  eq_or_eq : ∀ {p₁ p₂ : P} {l₁ l₂ : L}, p₁ ∈ l₁ → p₂ ∈ l₁ → p₁ ∈ l₂ → p₂ ∈ l₂ → p₁ = p₂ ∨ l₁ = l₂

class HasPoints extends Nondegenerate P L where
  /-- Intersection of two lines -/
  mkPoint : ∀ {l₁ l₂ : L}, l₁ ≠ l₂ → P
  mkPoint_ax : ∀ {l₁ l₂ : L} (h : l₁ ≠ l₂), mkPoint h ∈ l₁ ∧ mkPoint h ∈ l₂

class HasLines extends Nondegenerate P L where
  /-- Line through two points -/
  mkLine : ∀ {p₁ p₂ : P}, p₁ ≠ p₂ → L
  mkLine_ax : ∀ {p₁ p₂ : P} (h : p₁ ≠ p₂), p₁ ∈ mkLine h ∧ p₂ ∈ mkLine h

open Nondegenerate

open HasPoints (mkPoint mkPoint_ax)

open HasLines (mkLine mkLine_ax)

-- INSTANCE (free from Core): Dual.Nondegenerate

-- INSTANCE (free from Core): Dual.hasLines

-- INSTANCE (free from Core): Dual.hasPoints

theorem HasPoints.existsUnique_point [HasPoints P L] (l₁ l₂ : L) (hl : l₁ ≠ l₂) :
    ∃! p, p ∈ l₁ ∧ p ∈ l₂ :=
  ⟨mkPoint hl, mkPoint_ax hl, fun _ hp =>
    (eq_or_eq hp.1 (mkPoint_ax hl).1 hp.2 (mkPoint_ax hl).2).resolve_right hl⟩

theorem HasLines.existsUnique_line [HasLines P L] (p₁ p₂ : P) (hp : p₁ ≠ p₂) :
    ∃! l : L, p₁ ∈ l ∧ p₂ ∈ l :=
  HasPoints.existsUnique_point (Dual L) (Dual P) p₁ p₂ hp

variable {P L}

variable (L)

noncomputable def lineCount (p : P) : ℕ :=
  Nat.card { l : L // p ∈ l }

variable (P) {L}

noncomputable def pointCount (l : L) : ℕ :=
  Nat.card { p : P // p ∈ l }

variable (L)

theorem sum_lineCount_eq_sum_pointCount [Fintype P] [Fintype L] :
    ∑ p : P, lineCount L p = ∑ l : L, pointCount P l := by
  classical
    simp only [lineCount, pointCount, Nat.card_eq_fintype_card, ← Fintype.card_sigma]
    apply Fintype.card_congr
    calc
      (Σ p, { l : L // p ∈ l }) ≃ { x : P × L // x.1 ∈ x.2 } :=
        (Equiv.subtypeProdEquivSigmaSubtype (· ∈ ·)).symm
      _ ≃ { x : L × P // x.2 ∈ x.1 } := (Equiv.prodComm P L).subtypeEquiv fun x => Iff.rfl
      _ ≃ Σ l, { p // p ∈ l } := Equiv.subtypeProdEquivSigmaSubtype fun (l : L) (p : P) => p ∈ l

variable {P L}

theorem HasLines.pointCount_le_lineCount [HasLines P L] {p : P} {l : L} (h : p ∉ l)
    [Finite { l : L // p ∈ l }] : pointCount P l ≤ lineCount L p := by
  by_cases hf : Infinite { p : P // p ∈ l }
  · exact (le_of_eq Nat.card_eq_zero_of_infinite).trans (zero_le (lineCount L p))
  haveI := fintypeOfNotInfinite hf
  cases nonempty_fintype { l : L // p ∈ l }
  rw [lineCount, pointCount, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have : ∀ p' : { p // p ∈ l }, p ≠ p' := fun p' hp' => h ((congr_arg (· ∈ l) hp').mpr p'.2)
  exact
    Fintype.card_le_of_injective (fun p' => ⟨mkLine (this p'), (mkLine_ax (this p')).1⟩)
      fun p₁ p₂ hp =>
      Subtype.ext ((eq_or_eq p₁.2 p₂.2 (mkLine_ax (this p₁)).2
            ((congr_arg (_ ∈ ·) (Subtype.ext_iff.mp hp)).mpr (mkLine_ax (this p₂)).2)).resolve_right
          fun h' => (congr_arg (p ∉ ·) h').mp h (mkLine_ax (this p₁)).1)

theorem HasPoints.lineCount_le_pointCount [HasPoints P L] {p : P} {l : L} (h : p ∉ l)
    [hf : Finite { p : P // p ∈ l }] : lineCount L p ≤ pointCount P l :=
  @HasLines.pointCount_le_lineCount (Dual L) (Dual P) _ _ l p h hf

variable (P L)

theorem HasLines.card_le [HasLines P L] [Fintype P] [Fintype L] :
    Fintype.card P ≤ Fintype.card L := by
  classical
  by_contra hc₂
  obtain ⟨f, hf₁, hf₂⟩ := Nondegenerate.exists_injective_of_card_le (le_of_not_ge hc₂)
  have :=
    calc
      ∑ p, lineCount L p = ∑ l, pointCount P l := sum_lineCount_eq_sum_pointCount P L
      _ ≤ ∑ l, lineCount L (f l) :=
        (Finset.sum_le_sum fun l _ => HasLines.pointCount_le_lineCount (hf₂ l))
      _ = ∑ p ∈ univ.map ⟨f, hf₁⟩, lineCount L p := by rw [sum_map]; dsimp
      _ < ∑ p, lineCount L p := by
        obtain ⟨p, hp⟩ := not_forall.mp (mt (Fintype.card_le_of_surjective f) hc₂)
        refine sum_lt_sum_of_subset (subset_univ _) (mem_univ p) ?_ ?_ fun p _ _ ↦ zero_le _
        · simpa only [Finset.mem_map, exists_prop, Finset.mem_univ, true_and]
        · rw [lineCount, Nat.card_eq_fintype_card, Fintype.card_pos_iff]
          obtain ⟨l, _⟩ := @exists_line P L _ _ p
          exact
            let this := not_exists.mp hp l
            ⟨⟨mkLine this, (mkLine_ax this).2⟩⟩
  exact lt_irrefl _ this

theorem HasPoints.card_le [HasPoints P L] [Fintype P] [Fintype L] :
    Fintype.card L ≤ Fintype.card P :=
  @HasLines.card_le (Dual L) (Dual P) _ _ _ _

variable {P L}

theorem HasLines.exists_bijective_of_card_eq [HasLines P L] [Fintype P] [Fintype L]
    (h : Fintype.card P = Fintype.card L) :
    ∃ f : L → P, Function.Bijective f ∧ ∀ l, pointCount P l = lineCount L (f l) := by
  classical
    obtain ⟨f, hf1, hf2⟩ := Nondegenerate.exists_injective_of_card_le (ge_of_eq h)
    have hf3 := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf1, h.symm⟩
    exact ⟨f, hf3, fun l ↦ (sum_eq_sum_iff_of_le fun l _ ↦ pointCount_le_lineCount (hf2 l)).1
          ((hf3.sum_comp _).trans (sum_lineCount_eq_sum_pointCount P L)).symm _ <| mem_univ _⟩

theorem HasLines.lineCount_eq_pointCount [HasLines P L] [Fintype P] [Fintype L]
    (hPL : Fintype.card P = Fintype.card L) {p : P} {l : L} (hpl : p ∉ l) :
    lineCount L p = pointCount P l := by
  classical
    obtain ⟨f, hf1, hf2⟩ := HasLines.exists_bijective_of_card_eq hPL
    let s : Finset (P × L) := Set.toFinset { i | i.1 ∈ i.2 }
    have step1 : ∑ i : P × L, lineCount L i.1 = ∑ i : P × L, pointCount P i.2 := by
      rw [← Finset.univ_product_univ, Finset.sum_product_right, Finset.sum_product]
      simp_rw [Finset.sum_const, Finset.card_univ, hPL, sum_lineCount_eq_sum_pointCount]
    have step2 : ∑ i ∈ s, lineCount L i.1 = ∑ i ∈ s, pointCount P i.2 := by
      rw [s.sum_finset_product Finset.univ fun p => Set.toFinset { l | p ∈ l }]
      on_goal 1 =>
        rw [s.sum_finset_product_right Finset.univ fun l => Set.toFinset { p | p ∈ l }, eq_comm]
        · refine sum_bijective _ hf1 (by simp) fun l _ ↦ ?_
          simp_rw [hf2, sum_const, Set.toFinset_card, ← Nat.card_eq_fintype_card]
          change pointCount P l • _ = lineCount L (f l) • _
          rw [hf2]
      all_goals simp_rw [s, Finset.mem_univ, true_and, Set.mem_toFinset]; exact fun p => Iff.rfl
    have step3 : ∑ i ∈ sᶜ, lineCount L i.1 = ∑ i ∈ sᶜ, pointCount P i.2 := by
      rwa [← s.sum_add_sum_compl, ← s.sum_add_sum_compl, step2, add_left_cancel_iff] at step1
    rw [← Set.toFinset_compl] at step3
    exact
      ((Finset.sum_eq_sum_iff_of_le fun i hi =>
              HasLines.pointCount_le_lineCount (by exact Set.mem_toFinset.mp hi)).mp
          step3.symm (p, l) (Set.mem_toFinset.mpr hpl)).symm

theorem HasPoints.lineCount_eq_pointCount [HasPoints P L] [Fintype P] [Fintype L]
    (hPL : Fintype.card P = Fintype.card L) {p : P} {l : L} (hpl : p ∉ l) :
    lineCount L p = pointCount P l :=
  (@HasLines.lineCount_eq_pointCount (Dual L) (Dual P) _ _ _ _ hPL.symm l p hpl).symm
