/-
Extracted from Topology/Sheaves/Abelian.lean
Genuine: 2 of 8 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core

/-!
# Sheaves over Abelian categories
We provide instances for categories of sheaves over Abelian categories.

## Main Results

* `TopCat.Sheaf.exact_iff_stalkFunctor_map_exact`: A complex of sheaves over a concrete abelian
  category is exact if and only if it is exact on stalks.

-/

universe u v v₁ v₂

open TopologicalSpace CategoryTheory Limits

namespace TopCat

variable {X : TopCat.{u}}

variable {C : Type v₁} [Category.{v₂} C] [HasSheafify (Opens.grothendieckTopology X) C] [Abelian C]

-- INSTANCE (free from Core): :

namespace Sheaf

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): {D

end Sheaf

end

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): (p₀

namespace Sheaf

open Presheaf

variable {C : Type v} [Category.{u} C] [HasColimits C] [HasLimits C]
  {FC : C → C → Type*} {CC : C → Type u} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
  [instCC : ConcreteCategory C FC] [PreservesFilteredColimits (CategoryTheory.forget C)]
  [PreservesLimits (CategoryTheory.forget C)] [Abelian C]
  {X : TopCat.{u}} (p₀ : X)

-- INSTANCE (free from Core): :

open ZeroObject

include instCC in

lemma isZero_iff_stalkFunctor_obj_isZero (F : Sheaf C X) :
    IsZero F ↔ ∀ x : X, IsZero ((forget C X ⋙ stalkFunctor C x).obj F) := by
  refine ⟨fun h _ => Functor.map_isZero _ h, ?_⟩
  intro h
  let f : F ⟶ 0 := (isZero_zero (Sheaf C X)).from_ F
  have : IsIso f := by
    rw [Presheaf.isIso_iff_stalkFunctor_map_iso]
    exact fun x => isIso_of_source_target_iso_zero _ (h x).isoZero
      ((forget C X ⋙ stalkFunctor C x).map_isZero (isZero_zero _)).isoZero
  exact (isZero_zero _).of_iso (asIso f)

include instCC in

theorem exact_iff_stalkFunctor_map_exact (S : ShortComplex (Sheaf C X)) :
    S.Exact ↔ ∀ x : X, (S.map (forget C X ⋙ stalkFunctor C x)).Exact := by
  constructor
  · intro h x
    have := (forget C X ⋙ stalkFunctor C x).exact_tfae.out 2 1
    exact this.mp inferInstance S h
  intro h
  simp_rw [ShortComplex.exact_iff_isZero_homology] at h
  rw [ShortComplex.exact_iff_isZero_homology, isZero_iff_stalkFunctor_obj_isZero S.homology]
  exact fun x => (h x).of_iso
    (ShortComplex.mapHomologyIso S (forget C X ⋙ stalkFunctor C x)).symm

end Sheaf

end TopCat
