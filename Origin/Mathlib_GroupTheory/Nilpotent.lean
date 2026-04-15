/-
Extracted from GroupTheory/Nilpotent.lean
Genuine: 4 of 7 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!

# Nilpotent groups

An API for nilpotent groups, that is, groups for which the upper central series
reaches `⊤`.

## Main definitions

Recall that if `H K : Subgroup G` then `⁅H, K⁆ : Subgroup G` is the subgroup of `G` generated
by the commutators `hkh⁻¹k⁻¹`. Recall also Lean's conventions that `⊤` denotes the
subgroup `G` of `G`, and `⊥` denotes the trivial subgroup `{1}`.

* `upperCentralSeries G : ℕ → Subgroup G` : the upper central series of a group `G`.
     This is an increasing sequence of characteristic subgroups `H n` of `G` with `H 0 = ⊥` and
     `H (n + 1) / H n` is the centre of `G / H n`.
* `lowerCentralSeries G : ℕ → Subgroup G` : the lower central series of a group `G`.
     This is a decreasing sequence of characteristic subgroups `H n` of `G` with `H 0 = ⊤` and
     `H (n + 1) = ⁅H n, G⁆`.
* `IsNilpotent` : A group G is nilpotent if its upper central series reaches `⊤`, or
    equivalently if its lower central series reaches `⊥`.
* `Group.nilpotencyClass` : the length of the upper central series of a nilpotent group.
* `IsAscendingCentralSeries (H : ℕ → Subgroup G) : Prop` and
* `IsDescendingCentralSeries (H : ℕ → Subgroup G) : Prop` : Note that in the literature
    a "central series" for a group is usually defined to be a *finite* sequence of normal subgroups
    `H 0`, `H 1`, ..., starting at `⊤`, finishing at `⊥`, and with each `H n / H (n + 1)`
    central in `G / H (n + 1)`. In this formalisation it is convenient to have two weaker predicates
    on an infinite sequence of subgroups `H n` of `G`: we say a sequence is a *descending central
    series* if it starts at `G` and `⁅H n, ⊤⁆ ⊆ H (n + 1)` for all `n`. Note that this series
    may not terminate at `⊥`, and the `H i` need not be normal. Similarly a sequence is an
    *ascending central series* if `H 0 = ⊥` and `⁅H (n + 1), ⊤⁆ ⊆ H n` for all `n`, again with no
    requirement that the series reaches `⊤` or that the `H i` are normal.

## Main theorems

`G` is *defined* to be nilpotent if the upper central series reaches `⊤`.
* `nilpotent_iff_finite_ascending_central_series` : `G` is nilpotent iff some ascending central
    series reaches `⊤`.
* `nilpotent_iff_finite_descending_central_series` : `G` is nilpotent iff some descending central
    series reaches `⊥`.
* `nilpotent_iff_lower` : `G` is nilpotent iff the lower central series reaches `⊥`.
* The `Group.nilpotencyClass` can likewise be obtained from these equivalent
  definitions, see `least_ascending_central_series_length_eq_nilpotencyClass`,
  `least_descending_central_series_length_eq_nilpotencyClass` and
  `lowerCentralSeries_length_eq_nilpotencyClass`.
* If `G` is nilpotent, then so are its subgroups, images, quotients and preimages.
  Binary and finite products of nilpotent groups are nilpotent.
  Infinite products are nilpotent if their nilpotent class is bounded.
  Corresponding lemmas about the `Group.nilpotencyClass` are provided.
* The `Group.nilpotencyClass` of `G ⧸ center G` is given explicitly, and an induction principle
  is derived from that.
* `IsNilpotent.to_isSolvable`: If `G` is nilpotent, it is solvable.


## Warning

A "central series" is usually defined to be a finite sequence of normal subgroups going
from `⊥` to `⊤` with the property that each subquotient is contained within the centre of
the associated quotient of `G`. This means that if `G` is not nilpotent, then
none of what we have called `upperCentralSeries G`, `lowerCentralSeries G` or
the sequences satisfying `IsAscendingCentralSeries` or `IsDescendingCentralSeries`
are actually central series. Note that the fact that the upper and lower central series
are not central series if `G` is not nilpotent is a standard abuse of notation.

-/

open Subgroup

section WithGroup

variable {G : Type*} [Group G] (H : Subgroup G) [Normal H]

def upperCentralSeriesStep : Subgroup G where
  carrier := { x : G | ∀ y : G, x * y * x⁻¹ * y⁻¹ ∈ H }
  one_mem' y := by simp
  mul_mem' {a b} ha hb y := by
    convert Subgroup.mul_mem _ (ha (b * y * b⁻¹)) (hb y) using 1
    group
  inv_mem' {x} hx y := by
    specialize hx y⁻¹
    rw [mul_assoc, inv_inv] at hx ⊢
    exact Subgroup.Normal.mem_comm inferInstance hx

open QuotientGroup

theorem upperCentralSeriesStep_eq_comap_center :
    upperCentralSeriesStep H = Subgroup.comap (mk' H) (center (G ⧸ H)) := by
  ext
  rw [mem_comap, mem_center_iff, forall_mk]
  refine forall_congr' fun y => ?_
  rw [coe_mk', ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, eq_comm, eq_iff_div_mem,
    div_eq_mul_inv, mul_inv_rev, mul_assoc]

-- INSTANCE (free from Core): [H.Characteristic]

variable (G)

def upperCentralSeriesAux : ℕ → Σ' H : Subgroup G, Characteristic H
  | 0 => ⟨⊥, inferInstance⟩
  | n + 1 =>
    let un := upperCentralSeriesAux n
    let _un_characteristic := un.2
    ⟨upperCentralSeriesStep un.1, inferInstance⟩

def upperCentralSeries (n : ℕ) : Subgroup G :=
  (upperCentralSeriesAux G n).1

-- INSTANCE (free from Core): (n
