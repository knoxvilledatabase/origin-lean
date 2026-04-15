/-
Extracted from RingTheory/AdicCompletion/Completeness.lean
Genuine: 7 of 7 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Completeness of the Adic Completion for Finitely Generated Ideals

This file establishes that `AdicCompletion I M` is itself `I`-adically complete
when the ideal `I` is finitely generated.

## Main definitions

* `AdicCompletion.ofPowSMul`: The canonical inclusion between adic completions
  induced by the inclusion from `I ^ n • M` to `M`.

* `AdicCompletion.ofValEqZero`: Given `x` in `AdicCompletion I M` projecting to zero
  in `M / I ^ n • M`, `ofValEqZero` constructs the corresponding element in
  the adic completion of `I ^ n • M`.

## Main results

* `AdicCompletion.pow_smul_top_eq_ker_eval`: `I ^ n • AdicCompletion I M` is exactly the kernel
  of the evaluation map `eval I M n` when `I` is finitely generated.

* `AdicCompletion.isAdicComplete`: `AdicCompletion I M` is `I`-adically complete if `I` is
  finitely generated.

-/

noncomputable section

open Submodule Finsupp

variable {R : Type*} [CommRing R] (I : Ideal R)

variable {M : Type*} [AddCommGroup M] [Module R M]

variable {a b c : ℕ}

namespace AdicCompletion

variable (M) in

abbrev ofPowSMul (n : ℕ) : AdicCompletion I ↥(I ^ n • ⊤ : Submodule R M)
    →ₗ[AdicCompletion I R] AdicCompletion I M := map I (I ^ n • ⊤ : Submodule R M).subtype

theorem ofPowSMul_val_apply (h : c = b + a) {x : AdicCompletion I ↥(I ^ a • ⊤ : Submodule R M)} :
    (ofPowSMul I M a x).val c = powSMulQuotInclusion I M h ⊤ (x.val b) := by
  rw [← x.prop (show b ≤ c by lia), map_val_apply]
  refine Quotient.induction_on _ (x.val c) fun z ↦ ?_
  simp [powSMulQuotInclusion]

theorem ofPowSMul_val_apply_eq_zero (h : a ≤ b)
    {x : AdicCompletion I ↥(I ^ b • ⊤ : Submodule R M)} : (ofPowSMul I M b x).val a = 0 := by
  rw [map_val_apply]
  refine Quotient.induction_on _ (x.val a) fun z ↦ ?_
  simpa using pow_smul_top_le _ _ h z.prop

theorem ofPowSMul_injective (n : ℕ) : Function.Injective (ofPowSMul I M n) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx; ext i
  simp only [AdicCompletion.ext_iff, val_zero, Pi.zero_apply] at hx
  specialize hx (i + n)
  rw [ofPowSMul_val_apply I (by rw [add_comm]),
    LinearMap.map_eq_zero_iff _ (powSMulQuotInclusion_injective ..)] at hx
  simp [hx]

private lemma ofValEqZeroAux_exists {x : AdicCompletion I M} (h : c = b + a)
    (ha : x.val a = 0) : ∃ t, powSMulQuotInclusion I M h ⊤ t = x.val c := by
  simpa [← LinearMap.mem_range, range_powSMulQuotInclusion] using
    (val_apply_mem_smul_top_iff I (show a ≤ c by lia)).mpr ha

def ofValEqZeroAux {x : AdicCompletion I M} (h : c = b + a) (ha : x.val a = 0) :
    ↥(I ^ a • ⊤ : Submodule R M) ⧸ I ^ b • (⊤ : Submodule R ↥(I ^ a • ⊤ : Submodule R M)) :=
  Exists.choose (ofValEqZeroAux_exists I h ha)

private lemma ofValEqZeroAux_prop {x : AdicCompletion I M} (h : c = b + a)
    (ha : x.val a = 0) : (powSMulQuotInclusion I M h ⊤) (ofValEqZeroAux I h ha) = x.val c :=
  Exists.choose_spec (ofValEqZeroAux_exists I h ha)
