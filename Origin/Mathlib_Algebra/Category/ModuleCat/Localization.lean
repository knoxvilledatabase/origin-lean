/-
Extracted from Algebra/Category/ModuleCat/Localization.lean
Genuine: 2 of 6 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!

# Localized Module in ModuleCat

For a ring `R` satisfying `[Small.{v} R]` and a submonoid `S` of `R`,
this file defines an exact functor `ModuleCat.{v} R ⥤ ModuleCat.{v} (Localization S)`,
see `ModuleCat.localizedModuleFunctor`.

-/

universe v u

variable (R : Type u) [CommRing R]

open CategoryTheory

-- INSTANCE (free from Core): [Small.{v}

variable {R}

namespace ModuleCat

noncomputable def localizedModule [Small.{v} R] (M : ModuleCat.{v} R) (S : Submonoid R) :
    ModuleCat.{v} (Localization S) :=
  ModuleCat.of.{v} _ (Shrink.{v} (LocalizedModule S M))

-- INSTANCE (free from Core): [Small.{v}

-- INSTANCE (free from Core): [Small.{v}

noncomputable def localizedModuleMkLinearMap [Small.{v} R] (M : ModuleCat.{v} R)
    (S : Submonoid R) : M →ₗ[R] (M.localizedModule S) :=
  (Shrink.linearEquiv.{v} R _).symm.toLinearMap.comp (LocalizedModule.mkLinearMap S M)

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): localizedModule_isLocalizedModule
