/-
Extracted from LinearAlgebra/Dimension/LinearMap.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The rank of a linear map

## Main Definition
-  `LinearMap.rank`: The rank of a linear map.
-/

noncomputable section

universe u v v' v''

variable {K : Type u} {V V₁ : Type v} {V' V'₁ : Type v'} {V'' : Type v''}

open Cardinal Basis Submodule Function Set

namespace LinearMap

section Ring

variable [Ring K] [AddCommGroup V] [Module K V] [AddCommGroup V₁] [Module K V₁]

variable [AddCommGroup V'] [Module K V']

abbrev rank (f : V →ₗ[K] V') : Cardinal :=
  Module.rank K (LinearMap.range f)

theorem rank_le_range (f : V →ₗ[K] V') : rank f ≤ Module.rank K V' :=
  Submodule.rank_le _

theorem rank_le_domain (f : V →ₗ[K] V₁) : rank f ≤ Module.rank K V :=
  rank_range_le _
