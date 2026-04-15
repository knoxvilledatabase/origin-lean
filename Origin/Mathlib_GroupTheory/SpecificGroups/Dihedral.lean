/-
Extracted from GroupTheory/SpecificGroups/Dihedral.lean
Genuine: 4 of 6 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Dihedral Groups

We define the dihedral groups `DihedralGroup n`, with elements `r i` and `sr i` for `i : ZMod n`.

For `n ≠ 0`, `DihedralGroup n` represents the symmetry group of the regular `n`-gon. `r i`
represents the rotations of the `n`-gon by `2πi/n`, and `sr i` represents the reflections of the
`n`-gon. `DihedralGroup 0` corresponds to the infinite dihedral group.
-/

assert_not_exists Ideal TwoSidedIdeal

inductive DihedralGroup (n : ℕ) : Type
  | r : ZMod n → DihedralGroup n
  | sr : ZMod n → DihedralGroup n
  deriving DecidableEq

namespace DihedralGroup

variable {n : ℕ}

set_option backward.privateInPublic true in

private def mul : DihedralGroup n → DihedralGroup n → DihedralGroup n
  | r i, r j => r (i + j)
  | r i, sr j => sr (j - i)
  | sr i, r j => sr (i + j)
  | sr i, sr j => r (j - i)

set_option backward.privateInPublic true in

private def one : DihedralGroup n :=
  r 0

set_option backward.privateInPublic true in

set_option backward.privateInPublic.warn false in

-- INSTANCE (free from Core): :

set_option backward.privateInPublic true in

private def inv : DihedralGroup n → DihedralGroup n
  | r i => r (-i)
  | sr i => sr i

set_option backward.privateInPublic true in

set_option backward.privateInPublic.warn false in

-- INSTANCE (free from Core): :
