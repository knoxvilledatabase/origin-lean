/-
Extracted from Order/Filter/SmallSets.lean
Genuine: 14 of 16 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# The filter of small sets

This file defines the filter of small sets w.r.t. a filter `f`, which is the largest filter
containing all powersets of members of `f`.

`g` converges to `f.smallSets` if for all `s ∈ f`, eventually we have `g x ⊆ s`.

An example usage is that if `f : ι → E → ℝ` is a family of nonnegative functions with integral 1,
then saying that `fun i ↦ support (f i)` tendsto `(𝓝 0).smallSets` is a way of saying that
`f` tends to the Dirac delta distribution.
-/

assert_not_exists Set.Finite

open Filter

open Set

variable {α β : Type*} {ι : Sort*}

namespace Filter

variable {l l' la : Filter α} {lb : Filter β}

def smallSets (l : Filter α) : Filter (Set α) :=
  l.lift' powerset

theorem smallSets_eq_generate {f : Filter α} : f.smallSets = generate (powerset '' f.sets) := by
  simp_rw [generate_eq_biInf, smallSets, iInf_image, Filter.lift', Filter.lift, Function.comp_apply,
    Filter.mem_sets]

theorem bind_smallSets_gc :
    GaloisConnection (fun L : Filter (Set α) ↦ L.bind principal) smallSets := by
  intro L l
  simp_rw [smallSets_eq_generate, le_generate_iff, image_subset_iff]
  rfl

theorem hasBasis_smallSets (l : Filter α) :
    HasBasis l.smallSets (fun t : Set α => t ∈ l) powerset :=
  l.basis_sets.smallSets

theorem Eventually.exists_mem_basis_of_smallSets {p : ι → Prop} {s : ι → Set α} {P : Set α → Prop}
    (h₁ : ∀ᶠ t in l.smallSets, P t) (h₂ : HasBasis l p s) : ∃ i, p i ∧ P (s i) :=
  (h₂.smallSets.eventually_iff.mp h₁).imp fun _i ⟨hpi, hi⟩ ↦ ⟨hpi, hi Subset.rfl⟩

theorem Frequently.smallSets_of_forall_mem_basis {p : ι → Prop} {s : ι → Set α} {P : Set α → Prop}
    (h₁ : ∀ i, p i → P (s i)) (h₂ : HasBasis l p s) : ∃ᶠ t in l.smallSets, P t :=
  h₂.smallSets.frequently_iff.mpr fun _ hi => ⟨_, Subset.rfl, h₁ _ hi⟩

/-! No `Frequently.smallSets_of_forall_mem (h : ∀ s ∈ l, p s) : ∃ᶠ t in l.smallSets, p t` as
`Filter.frequently_smallSets_mem : ∃ᶠ t in l.smallSets, t ∈ l` is preferred. -/

theorem tendsto_smallSets_iff {f : α → Set β} :
    Tendsto f la lb.smallSets ↔ ∀ t ∈ lb, ∀ᶠ x in la, f x ⊆ t :=
  (hasBasis_smallSets lb).tendsto_right_iff

theorem eventually_smallSets {p : Set α → Prop} :
    (∀ᶠ s in l.smallSets, p s) ↔ ∃ s ∈ l, ∀ t, t ⊆ s → p t :=
  eventually_lift'_iff monotone_powerset

theorem eventually_smallSets' {p : Set α → Prop} (hp : ∀ ⦃s t⦄, s ⊆ t → p t → p s) :
    (∀ᶠ s in l.smallSets, p s) ↔ ∃ s ∈ l, p s :=
  eventually_smallSets.trans <|
    exists_congr fun s => Iff.rfl.and ⟨fun H => H s Subset.rfl, fun hs _t ht => hp ht hs⟩

theorem HasBasis.eventually_smallSets {α : Type*} {ι : Sort*} {p : ι → Prop} {l : Filter α}
    {s : ι → Set α} {q : Set α → Prop} {hl : l.HasBasis p s}
    (hq : ∀ ⦃s t : Set α⦄, s ⊆ t → q t → q s) :
    (∀ᶠ s in l.smallSets, q s) ↔ ∃ i, p i ∧ q (s i) := by
  rw [l.eventually_smallSets' hq, hl.exists_iff hq]

theorem frequently_smallSets {p : Set α → Prop} :
    (∃ᶠ s in l.smallSets, p s) ↔ ∀ t ∈ l, ∃ s, s ⊆ t ∧ p s :=
  l.hasBasis_smallSets.frequently_iff

theorem frequently_smallSets_mem (l : Filter α) : ∃ᶠ s in l.smallSets, s ∈ l :=
  frequently_smallSets.2 fun t ht => ⟨t, Subset.rfl, ht⟩

theorem frequently_smallSets' {α : Type*} {l : Filter α} {p : Set α → Prop}
    (hp : ∀ ⦃s t : Set α⦄, s ⊆ t → p s → p t) :
    (∃ᶠ s in l.smallSets, p s) ↔ ∀ t ∈ l, p t := by
  convert not_iff_not.mpr <| l.eventually_smallSets' (p := (¬ p ·)) (by tauto)
  simp

theorem HasBasis.frequently_smallSets {α : Type*} {ι : Sort*} {p : ι → Prop} {l : Filter α}
    {s : ι → Set α} {q : Set α → Prop} {hl : l.HasBasis p s}
    (hq : ∀ ⦃s t : Set α⦄, s ⊆ t → q s → q t) :
    (∃ᶠ s in l.smallSets, q s) ↔ ∀ i, p i → q (s i) := by
  rw [Filter.frequently_smallSets' hq, hl.forall_iff hq]
