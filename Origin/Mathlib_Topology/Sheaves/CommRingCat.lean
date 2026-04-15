/-
Extracted from Topology/Sheaves/CommRingCat.lean
Genuine: 2 of 5 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Sheaves of (commutative) rings.

Results specific to sheaves of commutative rings including sheaves of continuous functions
`TopCat.continuousFunctions` with natural operations of  `pullback` and `map` and
sub, quotient, and localization operations on sheaves of rings with
- `SubmonoidPresheaf` : A subpresheaf with a submonoid structure on each of the components.
- `LocalizationPresheaf` : The localization of a presheaf of commrings at a `SubmonoidPresheaf`.
- `TotalQuotientPresheaf` : The presheaf of total quotient rings.

As more results accumulate, please consider splitting this file.

## References
* https://stacks.math.columbia.edu/tag/0073
-/

universe u v w v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite

namespace TopCat.Presheaf

/-!
As an example, we now have everything we need to check the sheaf condition
for a presheaf of commutative rings, merely by checking the sheaf condition
for the underlying sheaf of types.

Note that the universes for `TopCat` and `CommRingCat` must be the same for this argument
to go through.
-/

example (X : TopCat.{u₁}) (F : Presheaf CommRingCat.{u₁} X)

    (h : Presheaf.IsSheaf (F ⋙ (forget CommRingCat))) :

    F.IsSheaf :=

(isSheaf_iff_isSheaf_comp (forget CommRingCat) F).mpr h

open AlgebraicGeometry in

section SubmonoidPresheaf

open scoped nonZeroDivisors

variable {X : TopCat.{w}} {C : Type u} [Category.{v} C]

structure SubmonoidPresheaf (F : X.Presheaf CommRingCat) where
  /-- The submonoid structure for each component -/
  obj : ∀ U, Submonoid (F.obj U)
  map : ∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V), obj U ≤ (obj V).comap (F.map i).hom

variable {F : X.Presheaf CommRingCat.{w}} (G : F.SubmonoidPresheaf)

protected noncomputable def SubmonoidPresheaf.localizationPresheaf : X.Presheaf CommRingCat where
  obj U := CommRingCat.of <| Localization (G.obj U)
  map {_ _} i := CommRingCat.ofHom <| IsLocalization.map _ (F.map i).hom (G.map i)
  map_id U := by
    simp_rw [F.map_id]
    ext x
    exact IsLocalization.map_id x
  map_comp {U V W} i j := by
    delta CommRingCat.ofHom CommRingCat.of Bundled.of
    simp_rw [F.map_comp]
    ext : 1
    dsimp
    rw [IsLocalization.map_comp_map]

-- INSTANCE (free from Core): (U)

-- INSTANCE (free from Core): (U)

set_option backward.isDefEq.respectTransparency false in
