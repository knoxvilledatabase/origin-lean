/-
Extracted from AlgebraicTopology/SimplicialSet/TopAdj.lean
Genuine: 5 of 8 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Properties of the geometric realization

In this file, we introduce some API in order to study the geometric
realization functor (and its right adjoint the singular simplicial set functor):
* `SimplexCategory.toTopHomeo`: the homeomorphism between the geometric
realization of `Δ[n]` and `stdSimplex ℝ (Fin (n + 1))`;
* `TopCat.toSSetObj₀Equiv : toSSet.obj X _⦋0⦌ ≃ X` for `X : TopCat`;
* `SSet.stdSimplex.toTopObjIsoI : |Δ[1]| ≅ TopCat.I`;
* `SSet.stdSimplex.toSSetObjI : Δ[1] ⟶ TopCat.toSSet.obj TopCat.I`:
the morphism corresponding to `toTopObjIsoI.hom` by adjunction.

-/

universe u

-- INSTANCE (free from Core): :

open CategoryTheory MonoidalCategory Simplicial Opposite

namespace SimplexCategory

open SSet

noncomputable def toTopHomeo (n : SimplexCategory) :
    |stdSimplex.{u}.obj n| ≃ₜ stdSimplex ℝ (Fin (n.len + 1)) :=
  (TopCat.homeoOfIso (toTopSimplex.{u}.app n)).trans Homeomorph.ulift

lemma toTopHomeo_naturality {n m : SimplexCategory} (f : n ⟶ m) :
    toTopHomeo m ∘ SSet.toTop.{u}.map (SSet.stdSimplex.map f) =
    stdSimplex.map f ∘ n.toTopHomeo := by
  ext x : 1
  exact ULift.up_injective (ConcreteCategory.congr_hom ((forget TopCat).congr_map
    (toTopSimplex.hom.naturality f)) x)

lemma toTopHomeo_naturality_apply {n m : SimplexCategory} (f : n ⟶ m)
    (x : |stdSimplex.obj n|) :
    m.toTopHomeo ((SSet.toTop.{u}.map (SSet.stdSimplex.map f) x)) =
      (_root_.stdSimplex.map f) (n.toTopHomeo x) :=
  congr_fun (toTopHomeo_naturality f) x

lemma toTopHomeo_symm_naturality {n m : SimplexCategory} (f : n ⟶ m) :
    m.toTopHomeo.symm ∘ stdSimplex.map f =
      (SSet.toTop.{u}.map (SSet.stdSimplex.map f)).hom ∘ n.toTopHomeo.symm := by
  ext x : 1
  exact ConcreteCategory.congr_hom ((forget _).congr_map
    (toTopSimplex.inv.naturality f)) _

lemma toTopHomeo_symm_naturality_apply {n m : SimplexCategory} (f : n ⟶ m)
    (x : stdSimplex ℝ (Fin (n.len + 1))) :
    m.toTopHomeo.symm (stdSimplex.map f x) =
      SSet.toTop.{u}.map (SSet.stdSimplex.map f) (n.toTopHomeo.symm x) :=
  congr_fun (toTopHomeo_symm_naturality f) x

end SimplexCategory

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

namespace TopCat
