/-
Extracted from Algebra/Category/ModuleCat/Simple.lean
Genuine: 3 of 5 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Simple objects in the category of `R`-modules

We prove simple modules are exactly simple objects in the category of `R`-modules.
-/

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

open CategoryTheory ModuleCat

theorem simple_iff_isSimpleModule : Simple (of R M) ↔ IsSimpleModule R M := by
  rw [simple_iff_subobject_isSimpleOrder, (subobjectModule (of R M)).isSimpleOrder_iff,
    isSimpleModule_iff]

theorem simple_iff_isSimpleModule' (M : ModuleCat R) : Simple M ↔ IsSimpleModule R M :=
  simple_iff_isSimpleModule

-- INSTANCE (free from Core): simple_of_isSimpleModule

-- INSTANCE (free from Core): isSimpleModule_of_simple

open Module

attribute [local instance] moduleOfAlgebraModule isScalarTower_of_algebra_moduleCat

theorem simple_of_finrank_eq_one {k : Type*} [Field k] [Algebra k R] {V : ModuleCat R}
    (h : finrank k V = 1) : Simple V :=
  (simple_iff_isSimpleModule' V).mpr <| (isSimpleModule_iff ..).mpr <|
    is_simple_module_of_finrank_eq_one h
