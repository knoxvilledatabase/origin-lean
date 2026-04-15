/-
Extracted from AlgebraicTopology/SingularSet.lean
Genuine: 7 of 10 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# The singular simplicial set of a topological space and geometric realization of a simplicial set

The *singular simplicial set* `TopCat.toSSet.obj X` of a topological space `X`
has `n`-simplices which identify to continuous maps `stdSimplex ℝ (Fin (n + 1)) → X`,
where `stdSimplex ℝ (Fin (n + 1))` is the standard topological `n`-simplex,
defined as the subtype of `Fin (n + 1) → ℝ` consisting of functions `f`
such that `0 ≤ f i` for all `i` and `∑ i, f i = 1`.

The *geometric realization* functor `SSet.toTop` is left adjoint to `TopCat.toSSet`.
It is the left Kan extension of `SimplexCategory.toTop` along the Yoneda embedding.

## Main definitions

* `TopCat.toSSet : TopCat ⥤ SSet` is the functor
  assigning the singular simplicial set to a topological space.
* `SSet.toTop : SSet ⥤ TopCat` is the functor
  assigning the geometric realization to a simplicial set.
* `sSetTopAdj : SSet.toTop ⊣ TopCat.toSSet` is the adjunction between these two functors.

## TODO (@joelriou)

- Show that the singular simplicial set is a Kan complex.
- Show the adjunction `sSetTopAdj` is a Quillen equivalence.

-/

universe u

open CategoryTheory

noncomputable def TopCat.toSSet : TopCat.{u} ⥤ SSet.{u} :=
  Presheaf.restrictedULiftYoneda.{0} SimplexCategory.toTop.{u}

noncomputable def TopCat.toSSetObjEquiv (X : TopCat.{u}) (n : SimplexCategoryᵒᵖ) :
    (toSSet.obj X).obj n ≃ C(stdSimplex ℝ (Fin (n.unop.len + 1)), X) :=
  Equiv.ulift.{0}.trans (ConcreteCategory.homEquiv.trans
    (Homeomorph.ulift.continuousMapCongr (.refl _)))

noncomputable def SSet.toTop : SSet.{u} ⥤ TopCat.{u} :=
  stdSimplex.{u}.leftKanExtension SimplexCategory.toTop

scoped[Simplicial] notation "|" X "|" => SSet.toTop.obj X

set_option backward.isDefEq.respectTransparency false in

noncomputable def sSetTopAdj : SSet.toTop.{u} ⊣ TopCat.toSSet.{u} :=
  Presheaf.uliftYonedaAdjunction
    (SSet.stdSimplex.{u}.leftKanExtension SimplexCategory.toTop)
    (SSet.stdSimplex.{u}.leftKanExtensionUnit SimplexCategory.toTop)

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

noncomputable def SSet.toTopSimplex :
    SSet.stdSimplex.{u} ⋙ SSet.toTop ≅ SimplexCategory.toTop :=
  Presheaf.isExtensionAlongULiftYoneda _

-- INSTANCE (free from Core): :

lemma sSetTopAdj_unit_app_app_down (S : SSet) (m : SimplexCategoryᵒᵖ) (a : S.obj m) :
    ((sSetTopAdj.unit.app S).app m a).down =
      SSet.toTopSimplex.inv.app _ ≫ SSet.toTop.map (SSet.yonedaEquiv.symm a) := by
  cat_disch

noncomputable def TopCat.toSSetIsoConst (X : TopCat.{u}) [TotallyDisconnectedSpace X] :
    TopCat.toSSet.obj X ≅ (Functor.const _).obj X :=
  (NatIso.ofComponents (fun n ↦ Equiv.toIso
    ((TotallyDisconnectedSpace.continuousMapEquivOfConnectedSpace _ X).symm.trans
      (X.toSSetObjEquiv n).symm))).symm
