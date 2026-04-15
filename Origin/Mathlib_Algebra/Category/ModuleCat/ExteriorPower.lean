/-
Extracted from Algebra/Category/ModuleCat/ExteriorPower.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The exterior powers as functors on the category of modules

In this file, given `M : ModuleCat R` and `n : ℕ`, we define `M.exteriorPower n : ModuleCat R`,
and this extends to a functor `ModuleCat.exteriorPower.functor : ModuleCat R ⥤ ModuleCat R`.

-/

universe v u

open CategoryTheory

namespace ModuleCat

variable {R : Type u} [CommRing R]

def exteriorPower (M : ModuleCat.{v} R) (n : ℕ) : ModuleCat.{max u v} R :=
  ModuleCat.of R (⋀[R]^n M)

def AlternatingMap (M : ModuleCat.{v} R) (N : ModuleCat.{max u v} R) (n : ℕ) :=
  _root_.AlternatingMap R M N (Fin n)

-- INSTANCE (free from Core): (M

namespace AlternatingMap

variable {M : ModuleCat.{v} R} {N : ModuleCat.{max u v} R} {n : ℕ}
