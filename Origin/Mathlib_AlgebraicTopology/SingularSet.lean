/-
Extracted from AlgebraicTopology/SingularSet.lean
Genuine: 4 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.AlgebraicTopology.TopologicalSimplex
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.Topology.Category.TopCat.Limits.Basic

/-!
# The singular simplicial set of a topological space and geometric realization of a simplicial set

The *singular simplicial set* `TopCat.toSSet.obj X` of a topological space `X`
has as `n`-simplices the continuous maps `[n].toTop → X`.
Here, `[n].toTop` is the standard topological `n`-simplex,
defined as `{ f : Fin (n+1) → ℝ≥0 // ∑ i, f i = 1 }` with its subspace topology.

The *geometric realization* functor `SSet.toTop.obj` is left adjoint to `TopCat.toSSet`.
It is the left Kan extension of `SimplexCategory.toTop` along the Yoneda embedding.

# Main definitions

* `TopCat.toSSet : TopCat ⥤ SSet` is the functor
  assigning the singular simplicial set to a topological space.
* `SSet.toTop : SSet ⥤ TopCat` is the functor
  assigning the geometric realization to a simplicial set.
* `sSetTopAdj : SSet.toTop ⊣ TopCat.toSSet` is the adjunction between these two functors.

## TODO

- Generalize to an adjunction between `SSet.{u}` and `TopCat.{u}` for any universe `u`
- Show that the singular simplicial set is a Kan complex.
- Show the adjunction `sSetTopAdj` is a Quillen adjunction.

-/

open CategoryTheory

noncomputable def TopCat.toSSet : TopCat ⥤ SSet :=
  Presheaf.restrictedYoneda SimplexCategory.toTop

noncomputable def SSet.toTop : SSet ⥤ TopCat :=
  yoneda.leftKanExtension SimplexCategory.toTop

noncomputable def sSetTopAdj : SSet.toTop ⊣ TopCat.toSSet :=
  Presheaf.yonedaAdjunction (yoneda.leftKanExtension SimplexCategory.toTop)
    (yoneda.leftKanExtensionUnit SimplexCategory.toTop)

noncomputable def SSet.toTopSimplex :
    (yoneda : SimplexCategory ⥤ _) ⋙ SSet.toTop ≅ SimplexCategory.toTop :=
  Presheaf.isExtensionAlongYoneda _
