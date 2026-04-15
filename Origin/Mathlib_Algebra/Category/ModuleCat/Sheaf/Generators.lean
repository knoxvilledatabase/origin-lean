/-
Extracted from Algebra/Category/ModuleCat/Sheaf/Generators.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Generating sections of sheaves of modules

In this file, given a sheaf of modules `M` over a sheaf of rings `R`, we introduce
the structure `M.GeneratingSections` which consists of a family of (global)
sections `s : I → M.sections` which generate `M`.

We also introduce the structure `M.LocalGeneratorsData` which contains the data
of a covering `X i` of the terminal object and the data of a
`(M.over (X i)).GeneratingSections` for all `i`. This is used in order to
define sheaves of modules of finite type.

## References

* https://stacks.math.columbia.edu/tag/01B4

-/

universe u v' u'

open CategoryTheory Limits

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

namespace SheafOfModules

variable (M N P : SheafOfModules.{u} R)

structure GeneratingSections where
  /-- the index type for the sections -/
  I : Type u
  /-- a family of sections which generate the sheaf of modules -/
  s : I → M.sections
  epi : Epi (M.freeHomEquiv.symm s) := by infer_instance

namespace GeneratingSections

attribute [instance] epi

variable {M N P}

noncomputable abbrev π (σ : M.GeneratingSections) : free σ.I ⟶ M := M.freeHomEquiv.symm σ.s
