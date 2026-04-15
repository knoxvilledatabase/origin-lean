/-
Extracted from Algebra/DirectSum/Module.lean
Genuine: 2 of 6 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Direct sum of modules

The first part of the file provides constructors for direct sums of modules. It provides a
construction of the direct sum using the universal property and proves its uniqueness
(`DirectSum.toModule.unique`).

The second part of the file covers the special case of direct sums of submodules of a fixed module
`M`.  There is a canonical linear map from this direct sum to `M` (`DirectSum.coeLinearMap`), and
the construction is of particular importance when this linear map is an equivalence; that is, when
the submodules provide an internal decomposition of `M`.  The property is defined more generally
elsewhere as `DirectSum.IsInternal`, but its basic consequences on `Submodule`s are established
in this file.

-/

universe u v w u₁

namespace DirectSum

open DirectSum Finsupp Module

section General

variable {R : Type u} [Semiring R]

variable {ι : Type v}

variable {M : ι → Type w} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): {S

-- INSTANCE (free from Core): {S

-- INSTANCE (free from Core): [∀

theorem smul_apply (b : R) (v : ⨁ i, M i) (i : ι) : (b • v) i = b • v i :=
  DFinsupp.smul_apply _ _ _

variable (R) in

def coeFnLinearMap : (⨁ i, M i) →ₗ[R] ∀ i, M i :=
  DFinsupp.coeFnLinearMap R
