/-
Extracted from CategoryTheory/Monoidal/Cartesian/CommGrp_.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Yoneda embedding of `CommGrp C`
-/

assert_not_exists Field

open CategoryTheory MonoidalCategory Limits Opposite CartesianMonoidalCategory MonObj

namespace CategoryTheory

universe w v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C] {X : C}

variable (X) in

class abbrev CommGrpObj := GrpObj X, IsCommMonObj X

variable (X) in
