/-
Extracted from Algebra/Category/ModuleCat/AB.lean
Genuine: 1 of 6 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!

# AB axioms in module categories

This file proves that the category of modules over a ring satisfies Grothendieck's axioms AB5, AB4,
and AB4*. Further, it proves that `R` is a separator in the category of modules over `R`, and
concludes that this category is Grothendieck abelian.
-/

universe u v

open CategoryTheory Limits

variable (R : Type u) [Ring R]

-- INSTANCE (free from Core): :

attribute [local instance] Abelian.hasFiniteBiproducts

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

lemma ModuleCat.isSeparator [Small.{v} R] : IsSeparator (ModuleCat.of.{v} R (Shrink.{v} R)) :=
    fun X Y f g h ↦ by
  simp only [ObjectProperty.singleton_iff, ModuleCat.hom_ext_iff, hom_comp,
    LinearMap.ext_iff, LinearMap.coe_comp, Function.comp_apply, forall_eq'] at h
  ext x
  simpa using h (ModuleCat.ofHom ((LinearMap.toSpanSingleton R X x).comp
    (Shrink.linearEquiv R R : Shrink R →ₗ[R] R))) 1

-- INSTANCE (free from Core): [Small.{v}

-- INSTANCE (free from Core): :
