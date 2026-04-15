/-
Extracted from Algebra/Module/LocalizedModule/Int.lean
Genuine: 10 of 10 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Integer elements of a localized module

This is a mirror of the corresponding notion for localizations of rings.

## Main definitions

* `IsLocalizedModule.IsInteger` is a predicate stating that `m : M'` is in the image of `M`

## Implementation details

After `IsLocalizedModule` and `IsLocalization` are unified, the two `IsInteger` predicates
can be unified.

-/

variable {R : Type*} [CommSemiring R] {S : Submonoid R} {M : Type*} [AddCommMonoid M]
  [Module R M] {M' : Type*} [AddCommMonoid M'] [Module R M'] (f : M →ₗ[R] M')

open Function

namespace IsLocalizedModule

def IsInteger (x : M') : Prop :=
  x ∈ LinearMap.range f

lemma isInteger_zero : IsInteger f (0 : M') :=
  Submodule.zero_mem _

theorem isInteger_add {x y : M'} (hx : IsInteger f x) (hy : IsInteger f y) : IsInteger f (x + y) :=
  Submodule.add_mem _ hx hy

theorem isInteger_smul {a : R} {x : M'} (hx : IsInteger f x) : IsInteger f (a • x) := by
  rcases hx with ⟨x', hx⟩
  use a • x'
  rw [← hx, LinearMapClass.map_smul]

variable (S)

variable [IsLocalizedModule S f]

theorem exists_integer_multiple (x : M') : ∃ a : S, IsInteger f (a.val • x) :=
  let ⟨⟨Num, denom⟩, h⟩ := IsLocalizedModule.surj S f x
  ⟨denom, Set.mem_range.mpr ⟨Num, h.symm⟩⟩

theorem exist_integer_multiples {ι : Type*} (s : Finset ι) (g : ι → M') :
    ∃ b : S, ∀ i ∈ s, IsInteger f (b.val • g i) := by
  classical
  choose sec hsec using (fun i ↦ IsLocalizedModule.surj S f (g i))
  refine ⟨∏ i ∈ s, (sec i).2, fun i hi => ⟨?_, ?_⟩⟩
  · exact (∏ j ∈ s.erase i, (sec j).2) • (sec i).1
  · simp only [LinearMap.map_smul_of_tower, Submonoid.coe_finset_prod]
    rw [← hsec, ← mul_smul, Submonoid.smul_def]
    congr
    simp only [Submonoid.coe_mul, Submonoid.coe_finset_prod, mul_comm]
    rw [← Finset.prod_insert (f := fun i ↦ ((sec i).snd).val) (s.notMem_erase i),
      Finset.insert_erase hi]

theorem exist_integer_multiples_of_finite {ι : Type*} [Finite ι] (g : ι → M') :
    ∃ b : S, ∀ i, IsInteger f ((b : R) • g i) := by
  cases nonempty_fintype ι
  obtain ⟨b, hb⟩ := exist_integer_multiples S f Finset.univ g
  exact ⟨b, fun i => hb i (Finset.mem_univ _)⟩

theorem exist_integer_multiples_of_finset (s : Finset M') :
    ∃ b : S, ∀ a ∈ s, IsInteger f ((b : R) • a) :=
  exist_integer_multiples S f s id

noncomputable def commonDenom {ι : Type*} (s : Finset ι) (g : ι → M') : S :=
  (exist_integer_multiples S f s g).choose

noncomputable def integerMultiple {ι : Type*} (s : Finset ι) (g : ι → M') (i : s) : M :=
  ((exist_integer_multiples S f s g).choose_spec i i.prop).choose
