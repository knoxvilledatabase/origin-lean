/-
Extracted from Algebra/Order/ToIntervalMod.lean
Genuine: 15 of 15 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Reducing to an interval modulo its length

This file defines operations that reduce a number (in an `Archimedean`
`LinearOrderedAddCommGroup`) to a number in a given interval, modulo the length of that
interval.

## Main definitions

* `toIcoDiv hp a b` (where `hp : 0 < p`): The unique integer such that this multiple of `p`,
  subtracted from `b`, is in `Ico a (a + p)`.
* `toIcoMod hp a b` (where `hp : 0 < p`): Reduce `b` to the interval `Ico a (a + p)`.
* `toIocDiv hp a b` (where `hp : 0 < p`): The unique integer such that this multiple of `p`,
  subtracted from `b`, is in `Ioc a (a + p)`.
* `toIocMod hp a b` (where `hp : 0 < p`): Reduce `b` to the interval `Ioc a (a + p)`.
-/

assert_not_exists TwoSidedIdeal

noncomputable section

section LinearOrderedAddCommGroup

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

include hp

def toIcoDiv (a b : α) : ℤ :=
  (existsUnique_sub_zsmul_mem_Ico hp b a).choose

theorem sub_toIcoDiv_zsmul_mem_Ico (a b : α) : b - toIcoDiv hp a b • p ∈ Set.Ico a (a + p) :=
  (existsUnique_sub_zsmul_mem_Ico hp b a).choose_spec.1

theorem toIcoDiv_eq_iff : toIcoDiv hp a b = n ↔ b - n • p ∈ Set.Ico a (a + p) :=
  (existsUnique_sub_zsmul_mem_Ico hp b a).choose_eq_iff

alias ⟨_, toIcoDiv_eq_of_sub_zsmul_mem_Ico⟩ := toIcoDiv_eq_iff

def toIocDiv (a b : α) : ℤ :=
  (existsUnique_sub_zsmul_mem_Ioc hp b a).choose

theorem sub_toIocDiv_zsmul_mem_Ioc (a b : α) : b - toIocDiv hp a b • p ∈ Set.Ioc a (a + p) :=
  (existsUnique_sub_zsmul_mem_Ioc hp b a).choose_spec.1

theorem toIocDiv_eq_iff : toIocDiv hp a b = n ↔ b - n • p ∈ Set.Ioc a (a + p) :=
  (existsUnique_sub_zsmul_mem_Ioc hp b a).choose_eq_iff

alias ⟨_, toIocDiv_eq_of_sub_zsmul_mem_Ioc⟩ := toIocDiv_eq_iff

def toIcoMod (a b : α) : α :=
  b - toIcoDiv hp a b • p

def toIocMod (a b : α) : α :=
  b - toIocDiv hp a b • p

theorem toIcoMod_mem_Ico (a b : α) : toIcoMod hp a b ∈ Set.Ico a (a + p) :=
  sub_toIcoDiv_zsmul_mem_Ico hp a b

theorem toIcoMod_mem_Ico' (b : α) : toIcoMod hp 0 b ∈ Set.Ico 0 p := by
  convert toIcoMod_mem_Ico hp 0 b
  exact (zero_add p).symm

theorem toIocMod_mem_Ioc (a b : α) : toIocMod hp a b ∈ Set.Ioc a (a + p) :=
  sub_toIocDiv_zsmul_mem_Ioc hp a b

theorem left_le_toIcoMod (a b : α) : a ≤ toIcoMod hp a b :=
  (Set.mem_Ico.1 (toIcoMod_mem_Ico hp a b)).1

theorem left_lt_toIocMod (a b : α) : a < toIocMod hp a b :=
  (Set.mem_Ioc.1 (toIocMod_mem_Ioc hp a b)).1

theorem toIcoMod_lt_right (a b : α) : toIcoMod hp a b < a + p :=
  (Set.mem_Ico.1 (toIcoMod_mem_Ico hp a b)).2

theorem toIocMod_le_right (a b : α) : toIocMod hp a b ≤ a + p :=
  (Set.mem_Ioc.1 (toIocMod_mem_Ioc hp a b)).2
