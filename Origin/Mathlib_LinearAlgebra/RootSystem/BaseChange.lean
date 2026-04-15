/-
Extracted from LinearAlgebra/RootSystem/BaseChange.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Base change for root pairings

When the coefficients are a field, root pairings behave well with respect to restriction and
extension of scalars.

## Main results:
* `RootPairing.restrict`: if `RootPairing.pairing` takes values in a subfield, we may restrict to
  get a root _system_ with coefficients in the subfield. Of particular interest is the case when
  the pairing takes values in its prime subfield (which happens for crystallographic pairings).

## TODO

* Extension of scalars
* Crystallographic root systems are isomorphic to base changes of root systems over `ℤ`: Take
  `M₀` and `N₀` to be the `ℤ`-span of roots and coroots.

-/

noncomputable section

open Set Function

open Submodule (span injective_subtype span subset_span span_setOf_mem_eq_top)

namespace RootPairing

class IsBalanced {ι R M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [CommRing R] [Module R M] [Module R N] (P : RootPairing ι R M N) : Prop where
  isPerfectCompl : P.toLinearMap.IsPerfectCompl (P.rootSpan R) (P.corootSpan R)

-- INSTANCE (free from Core): {ι

variable {ι L M N : Type*}
  [Field L] [AddCommGroup M] [AddCommGroup N] [Module L M] [Module L N]
  (P : RootPairing ι L M N)

section restrictScalars

variable (K : Type*) [Field K] [Algebra K L]
  [Module K M] [Module K N] [IsScalarTower K L M] [IsScalarTower K L N]
  [P.IsBalanced]

section SubfieldValued

variable [P.IsValuedIn K]

def restrictScalars' :
    RootPairing ι K (span K (range P.root)) (span K (range P.coroot)) where
  toLinearMap := .restrictScalarsRange₂ (R := L)
    (span K (range P.root)).subtype (span K (range P.coroot)).subtype (Algebra.linearMap K L)
    (FaithfulSMul.algebraMap_injective K L) P.toLinearMap fun x y ↦
      P.toLinearMap_apply_apply_mem_range_algebraMap K x x.property y y.property
  isPerfPair_toLinearMap := .restrictScalars_of_field P.toLinearMap _ _
    (injective_subtype _) (injective_subtype _) (by simpa using IsBalanced.isPerfectCompl) _
  root := ⟨fun i ↦ ⟨_, subset_span (mem_range_self i)⟩, fun i j h ↦ by simpa using h⟩
  coroot := ⟨fun i ↦ ⟨_, subset_span (mem_range_self i)⟩, fun i j h ↦ by simpa using h⟩
  root_coroot_two i := by
    have : algebraMap K L 2 = 2 := by
      rw [← Int.cast_two (R := K), ← Int.cast_two (R := L), map_intCast]
    exact FaithfulSMul.algebraMap_injective K L <| by simp [this]
  reflectionPerm := P.reflectionPerm
  reflectionPerm_root i j := by
    ext; simpa [algebra_compatible_smul L] using P.reflectionPerm_root i j
  reflectionPerm_coroot i j := by
    ext; simpa [algebra_compatible_smul L] using P.reflectionPerm_coroot i j

-- INSTANCE (free from Core): :
