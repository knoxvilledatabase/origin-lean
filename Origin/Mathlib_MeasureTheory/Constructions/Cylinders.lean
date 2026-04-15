/-
Extracted from MeasureTheory/Constructions/Cylinders.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# π-systems of cylinders and square cylinders

The instance `MeasurableSpace.pi` on `∀ i, α i`, where each `α i` has a `MeasurableSpace` `m i`,
is defined as `⨆ i, (m i).comap (fun a => a i)`.
That is, a function `g : β → ∀ i, α i` is measurable iff for all `i`, the function `b ↦ g b i`
is measurable.

We define two π-systems generating `MeasurableSpace.pi`, cylinders and square cylinders.

## Main definitions

Given a finite set `s` of indices, a cylinder is the product of a set of `∀ i : s, α i` and of
`univ` on the other indices. A square cylinder is a cylinder for which the set on `∀ i : s, α i` is
a product set.

* `cylinder s S`: cylinder with base set `S : Set (∀ i : s, α i)` where `s` is a `Finset`
* `squareCylinders C` with `C : ∀ i, Set (Set (α i))`: set of all square cylinders such that for
  all `i` in the finset defining the box, the projection to `α i` belongs to `C i`. The main
  application of this is with `C i = {s : Set (α i) | MeasurableSet s}`.
* `measurableCylinders`: set of all cylinders with measurable base sets.
* `cylinderEvents Δ`: The σ-algebra of cylinder events on `Δ`. It is the smallest σ-algebra making
  the projections on the `i`-th coordinate continuous for all `i ∈ Δ`.

## Main statements

* `generateFrom_squareCylinders`: square cylinders formed from measurable sets generate the product
  σ-algebra
* `generateFrom_measurableCylinders`: cylinders formed from measurable sets generate the
  product σ-algebra

-/

open Function Set MeasurableSpace

namespace MeasureTheory

variable {ι : Type _} {α : ι → Type _}

section squareCylinders

def squareCylinders (C : ∀ i, Set (Set (α i))) : Set (Set (∀ i, α i)) :=
  {S | ∃ s : Finset ι, ∃ t ∈ univ.pi C, S = (s : Set ι).pi t}

theorem squareCylinders_eq_iUnion_image (C : ∀ i, Set (Set (α i))) :
    squareCylinders C = ⋃ s : Finset ι, (fun t ↦ (s : Set ι).pi t) '' univ.pi C := by
  ext1 f
  simp only [squareCylinders, mem_iUnion, mem_image, mem_univ_pi, mem_setOf_eq,
    eq_comm (a := f)]

theorem isPiSystem_squareCylinders {C : ∀ i, Set (Set (α i))} (hC : ∀ i, IsPiSystem (C i))
    (hC_univ : ∀ i, univ ∈ C i) :
    IsPiSystem (squareCylinders C) := by
  rintro S₁ ⟨s₁, t₁, h₁, rfl⟩ S₂ ⟨s₂, t₂, h₂, rfl⟩ hst_nonempty
  classical
  let t₁' := s₁.piecewise t₁ (fun i ↦ univ)
  let t₂' := s₂.piecewise t₂ (fun i ↦ univ)
  have h1 : ∀ i ∈ (s₁ : Set ι), t₁ i = t₁' i :=
    fun i hi ↦ (Finset.piecewise_eq_of_mem _ _ _ hi).symm
  have h1' : ∀ i ∉ (s₁ : Set ι), t₁' i = univ :=
    fun i hi ↦ Finset.piecewise_eq_of_notMem _ _ _ hi
  have h2 : ∀ i ∈ (s₂ : Set ι), t₂ i = t₂' i :=
    fun i hi ↦ (Finset.piecewise_eq_of_mem _ _ _ hi).symm
  have h2' : ∀ i ∉ (s₂ : Set ι), t₂' i = univ :=
    fun i hi ↦ Finset.piecewise_eq_of_notMem _ _ _ hi
  rw [Set.pi_congr rfl h1, Set.pi_congr rfl h2, ← union_pi_inter h1' h2']
  refine ⟨s₁ ∪ s₂, fun i ↦ t₁' i ∩ t₂' i, ?_, ?_⟩
  · rw [mem_univ_pi]
    intro i
    have : (t₁' i ∩ t₂' i).Nonempty := by
      obtain ⟨f, hf⟩ := hst_nonempty
      rw [Set.pi_congr rfl h1, Set.pi_congr rfl h2, mem_inter_iff, mem_pi, mem_pi] at hf
      refine ⟨f i, ⟨?_, ?_⟩⟩
      · by_cases hi₁ : i ∈ s₁
        · exact hf.1 i hi₁
        · rw [h1' i hi₁]
          exact mem_univ _
      · by_cases hi₂ : i ∈ s₂
        · exact hf.2 i hi₂
        · rw [h2' i hi₂]
          exact mem_univ _
    refine hC i _ ?_ _ ?_ this
    · by_cases hi₁ : i ∈ s₁
      · rw [← h1 i hi₁]
        exact h₁ i (mem_univ _)
      · rw [h1' i hi₁]
        exact hC_univ i
    · by_cases hi₂ : i ∈ s₂
      · rw [← h2 i hi₂]
        exact h₂ i (mem_univ _)
      · rw [h2' i hi₂]
        exact hC_univ i
  · rw [Finset.coe_union]

theorem comap_eval_le_generateFrom_squareCylinders_singleton
    (α : ι → Type*) [m : ∀ i, MeasurableSpace (α i)] (i : ι) :
    MeasurableSpace.comap (Function.eval i) (m i) ≤
      MeasurableSpace.generateFrom
        ((fun t ↦ ({i} : Set ι).pi t) '' univ.pi fun i ↦ {s : Set (α i) | MeasurableSet s}) := by
  simp only [singleton_pi]
  rw [MeasurableSpace.comap_eq_generateFrom]
  refine MeasurableSpace.generateFrom_mono fun S ↦ ?_
  simp only [mem_setOf_eq, mem_image, mem_univ_pi, forall_exists_index, and_imp]
  intro t ht h
  classical
  refine ⟨fun j ↦ if hji : j = i then by convert t else univ, fun j ↦ ?_, ?_⟩
  · by_cases hji : j = i
    · simp only [hji, eq_mpr_eq_cast, dif_pos]
      convert ht
      simp only [cast_heq]
    · simp only [hji, not_false_iff, dif_neg, MeasurableSet.univ]
  · #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
    (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
    It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
    canonicalizer; a minimization would help. The original proof was: `grind` -/
    simp [h]

theorem generateFrom_squareCylinders [∀ i, MeasurableSpace (α i)] :
    MeasurableSpace.generateFrom (squareCylinders fun i ↦ {s : Set (α i) | MeasurableSet s}) =
      MeasurableSpace.pi := by
  apply le_antisymm
  · rw [MeasurableSpace.generateFrom_le_iff]
    rintro S ⟨s, t, h, rfl⟩
    simp only [mem_univ_pi, mem_setOf_eq] at h
    exact MeasurableSet.pi (Finset.countable_toSet _) (fun i _ ↦ h i)
  · refine iSup_le fun i ↦ ?_
    refine (comap_eval_le_generateFrom_squareCylinders_singleton α i).trans ?_
    refine MeasurableSpace.generateFrom_mono ?_
    rw [← Finset.coe_singleton, squareCylinders_eq_iUnion_image]
    exact subset_iUnion
      (fun (s : Finset ι) ↦
        (fun t : ∀ i, Set (α i) ↦ (s : Set ι).pi t) '' univ.pi (fun i ↦ setOf MeasurableSet))
      ({i} : Finset ι)

end squareCylinders

section cylinder

def cylinder (s : Finset ι) (S : Set (∀ i : s, α i)) : Set (∀ i, α i) :=
  s.restrict ⁻¹' S
