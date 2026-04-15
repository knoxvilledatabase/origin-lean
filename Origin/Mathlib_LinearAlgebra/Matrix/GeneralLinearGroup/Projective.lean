/-
Extracted from LinearAlgebra/Matrix/GeneralLinearGroup/Projective.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Projective general linear group

In this file we define `Matrix.ProjGenLinGroup n R` as the quotient of `GL n R` by its center.
We introduce notation `PGL(n, R)` for this group,
which works if `n` is either a finite type or a natural number.
If `n` is a number, then `PGL(n, R)` is interpreted as `PGL(Fin n, R)`.
-/

open scoped MatrixGroups

namespace Matrix

def ProjGenLinGroup (n : Type*) [Fintype n] [DecidableEq n] (R : Type*) [CommRing R] : Type _ :=
  GL n R ⧸ Subgroup.center (GL n R)
  deriving Group
