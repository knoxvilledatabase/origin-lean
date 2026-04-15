/-
Extracted from SetTheory/Cardinal/Continuum.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Cardinality of continuum

In this file we define `Cardinal.continuum` (notation: `𝔠`, localized in `Cardinal`) to be `2 ^ ℵ₀`.
We also prove some `simp` lemmas about cardinal arithmetic involving `𝔠`.

## Notation

- `𝔠` : notation for `Cardinal.continuum` in scope `Cardinal`.
-/

namespace Cardinal

universe u v

open Cardinal

def continuum : Cardinal.{u} :=
  2 ^ ℵ₀
