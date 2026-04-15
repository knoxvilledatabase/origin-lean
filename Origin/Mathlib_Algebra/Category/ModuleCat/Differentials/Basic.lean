/-
Extracted from Algebra/Category/ModuleCat/Differentials/Basic.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The differentials of a morphism in the category of commutative rings

In this file, given a morphism `f : A ⟶ B` in the category `CommRingCat`,
and `M : ModuleCat B`, we define the type `M.Derivation f` of
derivations with values in `M` relative to `f`.
We also construct the module of differentials
`CommRingCat.KaehlerDifferential f : ModuleCat B` and the corresponding derivation.

-/

universe v u

open CategoryTheory

attribute [local instance] IsScalarTower.of_compHom SMulCommClass.of_commMonoid

namespace ModuleCat

variable {A B : CommRingCat.{u}} (M : ModuleCat.{v} B) (f : A ⟶ B)

def Derivation : Type _ :=
  letI := f.hom.toAlgebra
  letI := Module.compHom M f.hom
  _root_.Derivation A B M

namespace Derivation

variable {M f}

def mk (d : B → M) (d_add : ∀ (b b' : B), d (b + b') = d b + d b' := by simp)
    (d_mul : ∀ (b b' : B), d (b * b') = b • d b' + b' • d b := by simp)
    (d_map : ∀ (a : A), d (f a) = 0 := by simp) :
    M.Derivation f :=
  letI := f.hom.toAlgebra
  letI := Module.compHom M f.hom
  { toFun := d
    map_add' := d_add
    map_smul' := fun a b ↦ by
      dsimp
      rw [RingHom.smul_toAlgebra, d_mul, d_map, smul_zero, add_zero]
      rfl
    map_one_eq_zero' := by
      dsimp
      rw [← f.hom.map_one, d_map]
    leibniz' := d_mul }

variable (D : M.Derivation f)

def d (b : B) : M :=
  letI := f.hom.toAlgebra
  letI := Module.compHom M f.hom
  _root_.Derivation.toLinearMap D b
