/-
Extracted from Algebra/Category/ModuleCat/Sheaf/Free.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Free sheaves of modules

In this file, we construct the functor
`SheafOfModules.freeFunctor : Type u ⥤ SheafOfModules.{u} R` which sends
a type `I` to the coproduct of copies indexed by `I` of `unit R`.

## TODO

* In case the category `C` has a terminal object `X`, promote `freeHomEquiv`
  into an adjunction between `freeFunctor` and the evaluation functor at `X`.
  (Alternatively, assuming specific universe parameters, we could show that
  `freeFunctor` is a left adjoint to `SheafOfModules.sectionsFunctor`.)

-/

universe u v₁ v₂ u₁ u₂

open CategoryTheory Limits

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

namespace SheafOfModules

noncomputable def free (I : Type u) : SheafOfModules.{u} R := ∐ (fun (_ : I) ↦ unit R)

noncomputable def ιFree {I : Type u} (i : I) : unit R ⟶ free I :=
  Sigma.ι (fun (_ : I) ↦ unit R) i

noncomputable def freeCofan (I : Type u) : Cofan (fun (_ : I) ↦ unit R) :=
  Cofan.mk (P := free I) ιFree
