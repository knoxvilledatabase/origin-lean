/-
Extracted from Topology/Category/Profinite/Extend.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Extending cones in `Profinite`

Let `(Sᵢ)_{i : I}` be a family of finite sets indexed by a cofiltered category `I` and let `S` be
its limit in `Profinite`. Let `G` be a functor from `Profinite` to a category `C` and suppose that
`G` preserves the limit described above. Suppose further that the projection maps `S ⟶ Sᵢ` are
epimorphic for all `i`. Then `G.obj S` is isomorphic to a limit indexed by
`StructuredArrow S toProfinite` (see `Profinite.Extend.isLimitCone`).

We also provide the dual result for a functor of the form `G : Profiniteᵒᵖ ⥤ C`.

We apply this to define `Profinite.diagram'`, `Profinite.asLimitCone'`, and `Profinite.asLimit'`,
analogues to their unprimed versions in `Mathlib/Topology/Category/Profinite/AsLimit.lean`, in which
the indexing category is `StructuredArrow S toProfinite` instead of `DiscreteQuotient S`.
-/

universe u w

open CategoryTheory Limits FintypeCat Functor

namespace Profinite

variable {I : Type u} [SmallCategory I] [IsCofiltered I]
    {F : I ⥤ FintypeCat.{max u w}} (c : Cone <| F ⋙ toProfinite)

lemma exists_hom (hc : IsLimit c) {X : FintypeCat} (f : c.pt ⟶ toProfinite.obj X) :
    ∃ (i : I) (g : F.obj i ⟶ X), f = c.π.app i ≫ toProfinite.map g := by
  let _ : TopologicalSpace X := ⊥
  have : DiscreteTopology (toProfinite.obj X) := ⟨rfl⟩
  let f' : LocallyConstant c.pt (toProfinite.obj X) :=
    ⟨f, (IsLocallyConstant.iff_continuous _).mpr f.hom.hom.continuous⟩
  obtain ⟨i, g, h⟩ := exists_locallyConstant.{_, u} c hc f'
  refine ⟨i, ⟨TypeCat.ofHom g⟩, ?_⟩
  ext x
  exact LocallyConstant.congr_fun h x

namespace Extend
