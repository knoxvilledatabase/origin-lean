/-
Extracted from SetTheory/Cardinal/ToNat.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Projection from cardinal numbers to natural numbers

In this file we define `Cardinal.toNat` to be the natural projection `Cardinal → ℕ`,
sending all infinite cardinals to zero.
We also prove basic lemmas about this definition.
-/

assert_not_exists Field

universe u v

open Function Set

namespace Cardinal

variable {α : Type u} {c d : Cardinal.{u}}

noncomputable def toNat : Cardinal →*₀ ℕ :=
  ENat.toNatHom.comp toENat
