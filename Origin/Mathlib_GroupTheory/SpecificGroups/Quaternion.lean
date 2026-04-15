/-
Extracted from GroupTheory/SpecificGroups/Quaternion.lean
Genuine: 4 of 6 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Quaternion Groups

We define the (generalised) quaternion groups `QuaternionGroup n` of order `4n`, also known as
dicyclic groups, with elements `a i` and `xa i` for `i : ZMod n`. The (generalised) quaternion
groups can be defined by the presentation
$\langle a, x | a^{2n} = 1, x^2 = a^n, x^{-1}ax=a^{-1}\rangle$. We write `a i` for
$a^i$ and `xa i` for $x * a^i$. For `n=2` the quaternion group `QuaternionGroup 2` is isomorphic to
the unit integral quaternions `(Quaternion ℤ)ˣ`.

## Main definition

`QuaternionGroup n`: The (generalised) quaternion group of order `4n`.

## Implementation notes

This file is heavily based on `DihedralGroup` by Shing Tak Lam.

In mathematics, the name "quaternion group" is reserved for the cases `n ≥ 2`. Since it would be
inconvenient to carry around this condition we define `QuaternionGroup` also for `n = 0` and
`n = 1`. `QuaternionGroup 0` is isomorphic to the infinite dihedral group, while
`QuaternionGroup 1` is isomorphic to a cyclic group of order `4`.

## References

* https://en.wikipedia.org/wiki/Dicyclic_group
* https://en.wikipedia.org/wiki/Quaternion_group

## TODO

Show that `QuaternionGroup 2 ≃* (Quaternion ℤ)ˣ`.

-/

inductive QuaternionGroup (n : ℕ) : Type
  | a : ZMod (2 * n) → QuaternionGroup n
  | xa : ZMod (2 * n) → QuaternionGroup n
  deriving DecidableEq

namespace QuaternionGroup

variable {n : ℕ}

set_option backward.privateInPublic true in

private def mul : QuaternionGroup n → QuaternionGroup n → QuaternionGroup n
  | a i, a j => a (i + j)
  | a i, xa j => xa (j - i)
  | xa i, a j => xa (i + j)
  | xa i, xa j => a (n + j - i)

set_option backward.privateInPublic true in

private def one : QuaternionGroup n :=
  a 0

set_option backward.privateInPublic true in

set_option backward.privateInPublic.warn false in

-- INSTANCE (free from Core): :

set_option backward.privateInPublic true in

private def inv : QuaternionGroup n → QuaternionGroup n
  | a i => a (-i)
  | xa i => xa (n + i)

set_option backward.privateInPublic true in

set_option backward.privateInPublic.warn false in

-- INSTANCE (free from Core): :
