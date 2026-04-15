/-
Extracted from LinearAlgebra/Charpoly/Basic.lean
Genuine: 7 | Conflates: 1 | Dissolved: 1 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.FieldTheory.Minpoly.Field

/-!

# Characteristic polynomial

We define the characteristic polynomial of `f : M →ₗ[R] M`, where `M` is a finite and
free `R`-module. The proof that `f.charpoly` is the characteristic polynomial of the matrix of `f`
in any basis is in `LinearAlgebra/Charpoly/ToMatrix`.

## Main definition

* `LinearMap.charpoly f` : the characteristic polynomial of `f : M →ₗ[R] M`.

-/

universe u v w

variable {R : Type u} {M : Type v} [CommRing R]

variable [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] (f : M →ₗ[R] M)

open Matrix Polynomial

noncomputable section

open Module.Free Polynomial Matrix

namespace LinearMap

section Basic

def charpoly : R[X] :=
  (toMatrix (chooseBasis R M) (chooseBasis R M) f).charpoly

theorem charpoly_def : f.charpoly = (toMatrix (chooseBasis R M) (chooseBasis R M) f).charpoly :=
  rfl

end Basic

section Coeff

theorem charpoly_monic : f.charpoly.Monic :=
  Matrix.charpoly_monic _

open Module in

-- CONFLATES (assumes ground = zero): charpoly_natDegree
lemma charpoly_natDegree [Nontrivial R] [StrongRankCondition R] :
    natDegree (charpoly f) = finrank R M := by
  rw [charpoly, Matrix.charpoly_natDegree_eq_dim, finrank_eq_card_chooseBasisIndex]

end Coeff

section CayleyHamilton

theorem aeval_self_charpoly : aeval f f.charpoly = 0 := by
  apply (LinearEquiv.map_eq_zero_iff (algEquivMatrix (chooseBasis R M)).toLinearEquiv).1
  rw [AlgEquiv.toLinearEquiv_apply, ← AlgEquiv.coe_algHom, ← Polynomial.aeval_algHom_apply _ _ _,
    charpoly_def]
  exact Matrix.aeval_self_charpoly _

theorem isIntegral : IsIntegral R f :=
  ⟨f.charpoly, ⟨charpoly_monic f, aeval_self_charpoly f⟩⟩

theorem minpoly_dvd_charpoly {K : Type u} {M : Type v} [Field K] [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] (f : M →ₗ[K] M) : minpoly K f ∣ f.charpoly :=
  minpoly.dvd _ _ (aeval_self_charpoly f)

theorem aeval_eq_aeval_mod_charpoly (p : R[X]) : aeval f p = aeval f (p %ₘ f.charpoly) :=
  (aeval_modByMonic_eq_self_of_root f.charpoly_monic f.aeval_self_charpoly).symm

theorem pow_eq_aeval_mod_charpoly (k : ℕ) : f ^ k = aeval f (X ^ k %ₘ f.charpoly) := by
  rw [← aeval_eq_aeval_mod_charpoly, map_pow, aeval_X]

variable {f}

-- DISSOLVED: minpoly_coeff_zero_of_injective

end CayleyHamilton

end LinearMap
