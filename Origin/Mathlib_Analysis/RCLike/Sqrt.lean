/-
Extracted from Analysis/RCLike/Sqrt.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Square root on `RCLike`

This file contains the definitions `Complex.sqrt` and `RCLike.sqrt` and builds basic API.
-/

variable {𝕜 : Type*} [RCLike 𝕜]

open ComplexOrder

noncomputable def Complex.sqrt (a : ℂ) : ℂ := a ^ (2⁻¹ : ℂ)
