/-
Extracted from Analysis/Calculus/FDeriv/Const.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Fréchet derivative of constant functions

This file contains the usual formulas (and existence assertions) for the derivative of constant
functions, including various special cases such as the functions `0`, `1`, `Nat.cast n`,
`Int.cast z`, and other numerals.

## Tags

derivative, differentiable, Fréchet, calculus

-/

open Asymptotics Function Filter Set Metric

open scoped Topology NNReal ENNReal

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]

variable {F : Type*} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

variable {f : E → F} {x : E} {s : Set E}

section Const

theorem hasFDerivAtFilter_const (c : F) (L : Filter (E × E)) :
    HasFDerivAtFilter (fun _ => c) (0 : E →L[𝕜] F) L :=
  .of_isLittleOTVS <| (IsLittleOTVS.zero _ _).congr_left fun _ => by simp

theorem hasFDerivAtFilter_zero (L : Filter (E × E)) :
    HasFDerivAtFilter (0 : E → F) (0 : E →L[𝕜] F) L := hasFDerivAtFilter_const _ _

theorem hasFDerivAtFilter_one [One F] (L : Filter (E × E)) :
    HasFDerivAtFilter (1 : E → F) (0 : E →L[𝕜] F) L := hasFDerivAtFilter_const _ _

theorem hasFDerivAtFilter_natCast [NatCast F] (n : ℕ) (L : Filter (E × E)) :
    HasFDerivAtFilter (n : E → F) (0 : E →L[𝕜] F) L :=
  hasFDerivAtFilter_const _ _

theorem hasFDerivAtFilter_intCast [IntCast F] (z : ℤ) (L : Filter (E × E)) :
    HasFDerivAtFilter (z : E → F) (0 : E →L[𝕜] F) L :=
  hasFDerivAtFilter_const _ _

theorem hasFDerivAtFilter_ofNat (n : ℕ) [OfNat F n] (L : Filter (E × E)) :
    HasFDerivAtFilter (ofNat(n) : E → F) (0 : E →L[𝕜] F) L :=
  hasFDerivAtFilter_const _ _
