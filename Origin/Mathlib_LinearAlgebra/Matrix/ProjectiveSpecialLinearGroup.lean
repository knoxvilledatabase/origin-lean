/-
Extracted from LinearAlgebra/Matrix/ProjectiveSpecialLinearGroup.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Projective Special Linear Group

## Notation

In the `MatrixGroups` locale:

* `PSL(n, R)` is a shorthand for `Matrix.ProjectiveSpecialLinearGroup (Fin n) R`
-/

namespace Matrix

universe u v

open Matrix LinearMap

open scoped MatrixGroups

variable (n : Type u) [DecidableEq n] [Fintype n] (R : Type v) [CommRing R]

abbrev ProjectiveSpecialLinearGroup : Type _ :=
    SpecialLinearGroup n R ⧸ Subgroup.center (SpecialLinearGroup n R)

scoped[MatrixGroups] notation "PSL(" n ", " R ")" => Matrix.ProjectiveSpecialLinearGroup (Fin n) R

end Matrix
