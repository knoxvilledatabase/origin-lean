/-
Extracted from Algebra/Category/ModuleCat/EnoughInjectives.lean
Genuine: 1 | Conflates: 0 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.Algebra.Category.Grp.EnoughInjectives
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.Logic.Equiv.TransferInstance

noncomputable section

/-!
# Category of $R$-modules has enough injectives

we lift enough injectives of abelian groups to arbitrary $R$-modules by adjoint functors
`restrictScalars ⊣ coextendScalars`
-/

open CategoryTheory

universe v u

variable (R : Type u) [Ring R]

instance : EnoughInjectives (ModuleCat.{v} ℤ) :=
  EnoughInjectives.of_equivalence (forget₂ (ModuleCat ℤ) AddCommGrp)

lemma ModuleCat.enoughInjectives : EnoughInjectives (ModuleCat.{max v u} R) :=
  EnoughInjectives.of_adjunction (ModuleCat.restrictCoextendScalarsAdj.{max v u} (algebraMap ℤ R))

open ModuleCat in

instance [UnivLE.{u,v}] : EnoughInjectives (ModuleCat.{v} R) :=
  letI := (equivShrink.{v} R).symm.ring
  letI := enoughInjectives.{v} (Shrink.{v} R)
  EnoughInjectives.of_equivalence (restrictScalars (equivShrink R).symm.ringEquiv.toRingHom)
