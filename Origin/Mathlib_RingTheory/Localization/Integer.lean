/-
Extracted from RingTheory/Localization/Integer.lean
Genuine: 13 of 13 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Integer elements of a localization

## Main definitions

* `IsLocalization.IsInteger` is a predicate stating that `x : S` is in the image of `R`

## Implementation notes

See `Mathlib/RingTheory/Localization/Basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/

variable {R : Type*} [CommSemiring R] {M : Submonoid R} {S : Type*} [CommSemiring S]

variable [Algebra R S] {P : Type*} [CommSemiring P]

open Function

namespace IsLocalization

variable (R)

def IsInteger (a : S) : Prop :=
  a ∈ (algebraMap R S).rangeS

end

theorem isInteger_zero : IsInteger R (0 : S) :=
  Subsemiring.zero_mem _

theorem isInteger_one : IsInteger R (1 : S) :=
  Subsemiring.one_mem _

theorem isInteger_add {a b : S} (ha : IsInteger R a) (hb : IsInteger R b) : IsInteger R (a + b) :=
  Subsemiring.add_mem _ ha hb

theorem isInteger_mul {a b : S} (ha : IsInteger R a) (hb : IsInteger R b) : IsInteger R (a * b) :=
  Subsemiring.mul_mem _ ha hb

theorem isInteger_smul {a : R} {b : S} (hb : IsInteger R b) : IsInteger R (a • b) := by
  rcases hb with ⟨b', hb⟩
  use a * b'
  rw [← hb, (algebraMap R S).map_mul, Algebra.smul_def]

variable (M)

variable [IsLocalization M S]

theorem exists_integer_multiple' (a : S) : ∃ b : M, IsInteger R (a * algebraMap R S b) :=
  let ⟨⟨Num, denom⟩, h⟩ := IsLocalization.surj _ a
  ⟨denom, Set.mem_range.mpr ⟨Num, h.symm⟩⟩

theorem exists_integer_multiple (a : S) : ∃ b : M, IsInteger R ((b : R) • a) := by
  simp_rw [Algebra.smul_def, mul_comm _ a]
  apply exists_integer_multiple'

theorem exist_integer_multiples {ι : Type*} (s : Finset ι) (f : ι → S) :
    ∃ b : M, ∀ i ∈ s, IsLocalization.IsInteger R ((b : R) • f i) := by
  haveI := Classical.propDecidable
  refine ⟨∏ i ∈ s, (sec M (f i)).2, fun i hi => ⟨?_, ?_⟩⟩
  · exact (∏ j ∈ s.erase i, (sec M (f j)).2) * (sec M (f i)).1
  rw [map_mul, sec_spec', ← mul_assoc, ← (algebraMap R S).map_mul, ← Algebra.smul_def]
  congr 2
  refine _root_.trans ?_ (map_prod (Submonoid.subtype M) _ _).symm
  rw [mul_comm, Submonoid.coe_finset_prod,
    -- Porting note: explicitly supplied `f`
    ← Finset.prod_insert (f := fun i => ((sec M (f i)).snd : R)) (s.notMem_erase i),
    Finset.insert_erase hi]
  rfl

theorem exist_integer_multiples_of_finite {ι : Type*} [Finite ι] (f : ι → S) :
    ∃ b : M, ∀ i, IsLocalization.IsInteger R ((b : R) • f i) := by
  cases nonempty_fintype ι
  obtain ⟨b, hb⟩ := exist_integer_multiples M Finset.univ f
  exact ⟨b, fun i => hb i (Finset.mem_univ _)⟩

theorem exist_integer_multiples_of_finset (s : Finset S) :
    ∃ b : M, ∀ a ∈ s, IsInteger R ((b : R) • a) :=
  exist_integer_multiples M s id

noncomputable def commonDenom {ι : Type*} (s : Finset ι) (f : ι → S) : M :=
  (exist_integer_multiples M s f).choose

noncomputable def integerMultiple {ι : Type*} (s : Finset ι) (f : ι → S) (i : s) : R :=
  ((exist_integer_multiples M s f).choose_spec i i.prop).choose
