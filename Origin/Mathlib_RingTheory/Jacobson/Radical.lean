/-
Extracted from RingTheory/Jacobson/Radical.lean
Genuine: 10 of 10 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Jacobson radical of modules and rings

## Main definitions

`Module.jacobson R M`: the Jacobson radical of a module `M` over a ring `R` is defined to be the
intersection of all maximal submodules of `M`.

`Ring.jacobson R`: the Jacobson radical of a ring `R` is the Jacobson radical of `R` as
an `R`-module, which is equal to the intersection of all maximal left ideals of `R`. It turns out
it is in fact a two-sided ideal, and equals the intersection of all maximal right ideals of `R`.

## Reference
* [F. Lorenz, *Algebra: Volume II: Fields with Structure, Algebras and Advanced Topics*][Lorenz2008]
-/

assert_not_exists Cardinal

namespace Module

open Submodule

variable (R R₂ M M₂ : Type*) [Ring R] [Ring R₂]

variable [AddCommGroup M] [Module R M] [AddCommGroup M₂] [Module R₂ M₂]

variable {τ₁₂ : R →+* R₂} [RingHomSurjective τ₁₂]

variable (f : M →ₛₗ[τ₁₂] M₂)

def jacobson : Submodule R M :=
  sInf { m : Submodule R M | IsCoatom m }

variable {R R₂ M M₂}

theorem le_comap_jacobson : jacobson R M ≤ comap f (jacobson R₂ M₂) := by
  conv_rhs => rw [jacobson, sInf_eq_iInf', comap_iInf]
  refine le_iInf_iff.mpr fun S m hm ↦ ?_
  obtain h | h := isCoatom_comap_or_eq_top f S.2
  · exact mem_sInf.mp hm _ h
  · simpa only [h] using mem_top

theorem map_jacobson_le : map f (jacobson R M) ≤ jacobson R₂ M₂ :=
  map_le_iff_le_comap.mpr (le_comap_jacobson f)

theorem jacobson_eq_bot_of_injective (inj : Function.Injective f) (h : jacobson R₂ M₂ = ⊥) :
    jacobson R M = ⊥ :=
  le_bot_iff.mp <| (le_comap_jacobson f).trans <| by
    simp_rw [h, comap_bot, (LinearMap.ker_eq_bot.mpr inj).le]

variable {f}

theorem map_jacobson_of_ker_le (surj : Function.Surjective f)
    (le : LinearMap.ker f ≤ jacobson R M) :
    map f (jacobson R M) = jacobson R₂ M₂ :=
  le_antisymm (map_jacobson_le f) <| by
    rw [jacobson, sInf_eq_iInf'] at le
    conv_rhs => rw [jacobson, sInf_eq_iInf', map_iInf_of_ker_le surj le]
    exact le_iInf fun m ↦ sInf_le (isCoatom_map_of_ker_le surj (le_iInf_iff.mp le m) m.2)

theorem comap_jacobson_of_ker_le (surj : Function.Surjective f)
    (le : LinearMap.ker f ≤ jacobson R M) :
    comap f (jacobson R₂ M₂) = jacobson R M := by
  rw [← map_jacobson_of_ker_le surj le, comap_map_eq_self le]

theorem map_jacobson_of_bijective (hf : Function.Bijective f) :
    map f (jacobson R M) = jacobson R₂ M₂ :=
  map_jacobson_of_ker_le hf.2 <| by simp_rw [LinearMap.ker_eq_bot.mpr hf.1, bot_le]

theorem comap_jacobson_of_bijective (hf : Function.Bijective f) :
    comap f (jacobson R₂ M₂) = jacobson R M :=
  comap_jacobson_of_ker_le hf.2 <| by simp_rw [LinearMap.ker_eq_bot.mpr hf.1, bot_le]

theorem jacobson_quotient_of_le {N : Submodule R M} (le : N ≤ jacobson R M) :
    jacobson R (M ⧸ N) = map N.mkQ (jacobson R M) :=
  (map_jacobson_of_ker_le N.mkQ_surjective <| by rwa [ker_mkQ]).symm

theorem jacobson_le_of_eq_bot {N : Submodule R M} (h : jacobson R (M ⧸ N) = ⊥) :
    jacobson R M ≤ N := by
  simp_rw [← N.ker_mkQ, ← comap_bot, ← h, le_comap_jacobson]

variable (R M)
