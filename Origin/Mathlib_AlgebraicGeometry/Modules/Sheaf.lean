/-
Extracted from AlgebraicGeometry/Modules/Sheaf.lean
Genuine: 1 | Conflates: 0 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.AlgebraicGeometry.Modules.Presheaf

/-!
# The category of sheaves of modules over a scheme

In this file, we define the abelian category of sheaves of modules
`X.Modules` over a scheme `X`.

-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

abbrev Modules := SheafOfModules.{u} X.ringCatSheaf

noncomputable instance : Abelian X.Modules := inferInstance

end AlgebraicGeometry.Scheme
