/-
Extracted from Algebra/Category/ModuleCat/Topology/Basic.lean
Genuine: 5 of 9 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# The category `TopModuleCat R` of topological modules

We define `TopModuleCat R`, the category of topological modules, and show that
it has all limits and colimits.

We also provide various adjunctions:
- `TopModuleCat.withModuleTopologyAdj`:
  equipping the module topology is left adjoint to the forgetful functor into `ModuleCat R`.
- `TopModuleCat.indiscreteAdj`:
  equipping the indiscrete topology is right adjoint to the forgetful functor into `ModuleCat R`.
- `TopModuleCat.freeAdj`:
  the free-forgetful adjunction between `TopModuleCat R` and `TopCat`.

## Future projects
Show that the forgetful functor to `TopCat` preserves filtered colimits.
-/

universe v u

variable (R : Type u) [Ring R] [TopologicalSpace R]

open CategoryTheory ConcreteCategory

structure TopModuleCat extends ModuleCat.{v} R where
  /-- The underlying topological space. -/
  [topologicalSpace : TopologicalSpace carrier]
  [isTopologicalAddGroup : IsTopologicalAddGroup carrier]
  [continuousSMul : ContinuousSMul R carrier]

namespace TopModuleCat

-- INSTANCE (free from Core): :

attribute [instance] topologicalSpace isTopologicalAddGroup continuousSMul

abbrev of (M : Type v) [AddCommGroup M] [Module R M] [TopologicalSpace M] [ContinuousAdd M]
    [ContinuousSMul R M] : TopModuleCat R :=
  have : ContinuousNeg M := ⟨by convert continuous_const_smul (-1 : R) (T := M); ext; simp⟩
  have : IsTopologicalAddGroup M := ⟨⟩
  ⟨.of R M⟩

set_option backward.privateInPublic true in

variable {R} in

structure Hom (X Y : TopModuleCat.{v} R) where
  -- use `ofHom` instead
  private ofHom' ::
  /-- The underlying continuous linear map. Use `hom` instead. -/
  hom' : X →L[R] Y

set_option backward.privateInPublic true in

set_option backward.privateInPublic.warn false in

-- INSTANCE (free from Core): :

set_option linter.style.whitespace false in -- manual alignment is not recognised

set_option backward.privateInPublic true in

set_option backward.privateInPublic.warn false in

-- INSTANCE (free from Core): :

variable {R} in

abbrev Hom.hom {X Y : TopModuleCat R} (f : X.Hom Y) : X →L[R] Y :=
  ConcreteCategory.hom (C := TopModuleCat R) f

variable {R} in

abbrev ofHom {X Y : Type v}
    [AddCommGroup X] [Module R X] [TopologicalSpace X] [ContinuousAdd X] [ContinuousSMul R X]
    [AddCommGroup Y] [Module R Y] [TopologicalSpace Y] [ContinuousAdd Y] [ContinuousSMul R Y]
    (f : X →L[R] Y) : of R X ⟶ of R Y :=
  ConcreteCategory.ofHom f
