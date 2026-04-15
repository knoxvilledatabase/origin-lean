/-
Extracted from Order/Sublocale.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Sublocale

Locales are the dual concept to frames. Locale theory is a branch of point-free topology, where
intuitively locales are like topological spaces which may or may not have enough points.
Sublocales of a locale generalize the concept of subspaces in topology to the point-free setting.

## TODO

Create separate definitions for `sInf_mem` and `HImpClosed` (also useful for `CompleteSublattice`)

## References

* [J. Picada A. Pultr, *Frames and Locales*][picado2012]
* https://ncatlab.org/nlab/show/sublocale
* https://ncatlab.org/nlab/show/nucleus
-/

variable {X : Type*} [Order.Frame X]

open Set

structure Sublocale (X : Type*) [Order.Frame X] where
  /-- The set corresponding to the sublocale. -/
  carrier : Set X
  /-- A sublocale is closed under all meets.

  Do NOT use directly. Use `Sublocale.sInf_mem` instead. -/
  sInf_mem' : ∀ s ⊆ carrier, sInf s ∈ carrier
  /-- A sublocale is closed under heyting implication.

  Do NOT use directly. Use `Sublocale.himp_mem` instead. -/
  himp_mem' : ∀ a b, b ∈ carrier → a ⇨ b ∈ carrier

namespace Sublocale

variable {ι : Sort*} {S T : Sublocale X} {s : Set X} {f : ι → X} {a b : X}

-- INSTANCE (free from Core): instSetLike

-- INSTANCE (free from Core): :
