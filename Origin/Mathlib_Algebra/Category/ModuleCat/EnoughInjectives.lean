/-
Extracted from Algebra/Category/ModuleCat/EnoughInjectives.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Category of $R$-modules has enough injectives

We lift enough injectives of abelian groups to arbitrary $R$-modules by adjoint functors
`restrictScalars ⊣ coextendScalars`
-/

open CategoryTheory

universe v u

variable (R : Type u) [Ring R]

-- INSTANCE (free from Core): :

lemma ModuleCat.enoughInjectives : EnoughInjectives (ModuleCat.{max v u} R) :=
  EnoughInjectives.of_adjunction (ModuleCat.restrictCoextendScalarsAdj.{max v u} (algebraMap ℤ R))

open ModuleCat in

-- INSTANCE (free from Core): [Small.{v}
