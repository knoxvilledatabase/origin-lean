/-
Extracted from Algebra/Category/FGModuleCat/EssentiallySmall.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# The category of finitely generated modules over a ring is essentially small

This file proves that `FGModuleCat R`, the category of finitely generated modules over a ring `R`,
is essentially small, by providing an explicit small model. However, for applications, it is
recommended to use the standard `CategoryTheory.SmallModel (FGModuleCat R)` instead.

-/

universe v w u

variable (R : Type u) [CommRing R]

open CategoryTheory

structure FGModuleRepr : Type u where
  /-- The natural number `n` that defines the module as a quotient of `Fin n → R` (i.e. `R^n`). -/
  (n : ℕ)
  /-- The kernel of the surjective map from `Fin n → R` (i.e. `R^n`) to the module represented. -/
  (S : Submodule R (Fin n → R))

namespace FGModuleRepr

variable (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]

variable {R} in

def repr (x : FGModuleRepr R) : Type u :=
  _ ⧸ x.S

deriving AddCommGroup, Module R

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): (x
