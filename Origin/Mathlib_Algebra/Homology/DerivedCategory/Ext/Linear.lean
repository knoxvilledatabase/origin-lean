/-
Extracted from Algebra/Homology/DerivedCategory/Ext/Linear.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Ext-modules in linear categories

In this file, we show that if `C` is an `R`-linear abelian category,
then there is an `R`-module structure on the groups `Ext X Y n`
for `X` and `Y` in `C` and `n : ℕ`.

-/

universe w' w t v u

namespace CategoryTheory

namespace Abelian

namespace Ext

section Ring

variable {R : Type t} [Ring R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  [HasExt.{w} C]

variable {X Y : C} {n : ℕ}

-- INSTANCE (free from Core): :

lemma smul_eq_comp_mk₀ (x : Ext X Y n) (r : R) :
    r • x = x.comp (mk₀ (r • 𝟙 Y)) (add_zero _) := by
  let := HasDerivedCategory.standard C
  ext
  apply ((Equiv.linearEquiv R homEquiv).map_smul r x).trans
  change r • homEquiv x = (x.comp (mk₀ (r • 𝟙 Y)) (add_zero _)).hom
  rw [comp_hom, mk₀_hom, Functor.map_smul, Functor.map_id, ShiftedHom.mk₀_smul,
    ShiftedHom.comp_smul, ShiftedHom.comp_mk₀_id]
