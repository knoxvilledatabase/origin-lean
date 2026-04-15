/-
Extracted from Algebra/Category/Grp/IsFinite.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The Serre class of finite abelian groups

In this file, we define `isFinite : ObjectProperty AddCommGrpCat` and show
that it is a Serre class.

-/

universe u

open CategoryTheory Limits ZeroObject

namespace AddCommGrpCat

def isFinite : ObjectProperty AddCommGrpCat.{u} :=
  fun M ↦ Finite M
