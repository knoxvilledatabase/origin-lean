/-
Extracted from Analysis/Asymptotics/AsymptoticEquivalent.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Asymptotic equivalence

In this file, we prove properties of the relation `IsEquivalent l u v`,
which means that `u-v` is little o of `v` along the filter `l`.

Unlike `Is(Little|Big)O` relations, this one requires `u` and `v` to have the same codomain `β`.

## Notation

We use the notation `u ~[l] v := IsEquivalent l u v`, which you can use by opening the
`Asymptotics` locale.

## Main results

If `β` is a `NormedAddCommGroup` :

- `_ ~[l] _` is an equivalence relation
- Equivalent statements for `u ~[l] const _ c` :
  - If `c ≠ 0`, this is true iff `Tendsto u l (𝓝 c)` (see `isEquivalent_const_iff_tendsto`)
  - For `c = 0`, this is true iff `u =ᶠ[l] 0` (see `isEquivalent_zero_iff_eventually_zero`)

If `β` is a `NormedField` :

- Alternative characterization of the relation (see `isEquivalent_iff_exists_eq_mul`) :

  `u ~[l] v ↔ ∃ (φ : α → β) (hφ : Tendsto φ l (𝓝 1)), u =ᶠ[l] φ * v`

- Provided some non-vanishing hypothesis, this can be seen as `u ~[l] v ↔ Tendsto (u/v) l (𝓝 1)`
  (see `isEquivalent_iff_tendsto_one`)
- For any constant `c`, `u ~[l] v` implies `Tendsto u l (𝓝 c) ↔ Tendsto v l (𝓝 c)`
  (see `IsEquivalent.tendsto_nhds_iff`)
- `*` and `/` are compatible with `_ ~[l] _` (see `IsEquivalent.mul` and `IsEquivalent.div`)

If `β` is a `NormedLinearOrderedField` :

- If `u ~[l] v`, we have `Tendsto u l atTop ↔ Tendsto v l atTop`
  (see `IsEquivalent.tendsto_atTop_iff`)

## Implementation Notes

Note that `IsEquivalent` takes the parameters `(l : Filter α) (u v : α → β)` in that order.
This is to enable `calc` support, as `calc` requires that the last two explicit arguments are `u v`.

-/

namespace Asymptotics

open Filter Function

open Topology

section NormedAddCommGroup

variable {α β : Type*} [NormedAddCommGroup β]

variable {u v w : α → β} {l : Filter α}

nonrec theorem IsEquivalent.isBigO (h : u ~[l] v) : u =O[l] v :=
  (IsBigO.congr_of_sub h.isBigO.symm).mp (isBigO_refl _ _)

theorem IsEquivalent.isBigO_symm (h : u ~[l] v) : v =O[l] u := by
  convert h.isLittleO.right_isBigO_add
  simp

theorem IsEquivalent.isTheta (h : u ~[l] v) : u =Θ[l] v :=
  ⟨h.isBigO, h.isBigO_symm⟩

theorem IsEquivalent.isTheta_symm (h : u ~[l] v) : v =Θ[l] u :=
  ⟨h.isBigO_symm, h.isBigO⟩
