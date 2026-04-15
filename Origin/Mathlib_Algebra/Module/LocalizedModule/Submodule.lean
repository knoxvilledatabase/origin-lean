/-
Extracted from Algebra/Module/LocalizedModule/Submodule.lean
Genuine: 6 of 9 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Localization of Submodules

Results about localizations of submodules and quotient modules are provided in this file.

## Main results
- `Submodule.localized`:
  The localization of an `R`-submodule of `M` at `p` viewed as an `Rₚ`-submodule of `Mₚ`.
  A direct consequence of this is that `Rₚ` is flat over `R`; see `IsLocalization.flat`.
- `Submodule.toLocalized`:
  The localization map of a submodule `M' →ₗ[R] M'.localized p`.
- `Submodule.toLocalizedQuotient`:
  The localization map of a quotient module `M ⧸ M' →ₗ[R] LocalizedModule p M ⧸ M'.localized p`.

## TODO
- Statements regarding the exactness of localization.

-/

open nonZeroDivisors

variable {R S M N : Type*}

variable (S) [CommSemiring R] [CommSemiring S] [AddCommMonoid M] [AddCommMonoid N]

variable [Module R M] [Module R N] [Algebra R S] [Module S N] [IsScalarTower R S N]

variable (p : Submonoid R) [IsLocalization p S] (f : M →ₗ[R] N) [IsLocalizedModule p f]

variable (M' M'' : Submodule R M)

namespace Submodule

def localized₀ : Submodule R N where
  carrier := { x | ∃ m ∈ M', ∃ s : p, IsLocalizedModule.mk' f m s = x }
  add_mem' := fun {x y} ⟨m, hm, s, hx⟩ ⟨n, hn, t, hy⟩ ↦ ⟨t • m + s • n, add_mem (M'.smul_mem t hm)
    (M'.smul_mem s hn), s * t, by rw [← hx, ← hy, IsLocalizedModule.mk'_add_mk']⟩
  zero_mem' := ⟨0, zero_mem _, 1, by simp⟩
  smul_mem' r x := by
    rintro ⟨m, hm, s, hx⟩
    exact ⟨r • m, smul_mem M' _ hm, s, by rw [IsLocalizedModule.mk'_smul, hx]⟩

def localized' : Submodule S N where
  __ := localized₀ p f M'
  smul_mem' := fun r x ⟨m, hm, s, hx⟩ ↦ by
    have ⟨y, t, hyt⟩ := IsLocalization.exists_mk'_eq p r
    exact ⟨y • m, M'.smul_mem y hm, t * s, by simp [← hyt, ← hx, IsLocalizedModule.mk'_smul_mk']⟩

theorem localized'_eq_span : localized' S p f M' = span S (f '' M') := by
  refine le_antisymm ?_ (span_le.mpr <| by rintro _ ⟨m, hm, rfl⟩; exact ⟨m, hm, 1, by simp⟩)
  rintro _ ⟨m, hm, s, rfl⟩
  rw [← one_smul R m, ← mul_one s, ← IsLocalizedModule.mk'_smul_mk' S]
  exact smul_mem _ _ (subset_span ⟨m, hm, by simp⟩)

theorem map_le_localized₀ : M'.map f ≤ localized₀ p f M' := by
  rintro - ⟨x, hx, rfl⟩
  rw [mem_localized₀]
  exact ⟨x, hx, 1, IsLocalizedModule.mk'_one p f x⟩

def localized'gi : GaloisInsertion (localized' S p f) (comap f <| ·.restrictScalars R) where
  gc M' N' := ⟨fun h m hm ↦ h ⟨m, hm, 1, by simp⟩, fun h ↦ by
    rw [localized'_eq_span, span_le]; apply map_le_iff_le_comap.mpr h⟩
  le_l_u N' n hn := by
    obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective p f n
    refine ⟨m, ?_, s, rfl⟩
    rw [mem_comap, restrictScalars_mem, ← IsLocalizedModule.mk'_cancel' _ _ s,
      Submonoid.smul_def, ← algebraMap_smul S]
    exact smul_mem _ _ hn
  choice x _ := localized' S p f x
  choice_eq _ _ := rfl

noncomputable abbrev localized : Submodule (Localization p) (LocalizedModule p M) :=
  M'.localized' (Localization p) p (LocalizedModule.mkLinearMap p M)
