/-
Extracted from CategoryTheory/Abelian/Transfer.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Transferring "abelian-ness" across a functor

If `C` is an additive category, `D` is an abelian category,
we have `F : C ⥤ D` `G : D ⥤ C` (both preserving zero morphisms),
`G` is left exact (that is, preserves finite limits),
and further we have `adj : G ⊣ F` and `i : F ⋙ G ≅ 𝟭 C`,
then `C` is also abelian.

A particular example is the transfer of `Abelian` instances from a category `C` to `ShrinkHoms C`;
see `ShrinkHoms.abelian`. In this case, we also transfer the `Preadditive` structure.

See <https://stacks.math.columbia.edu/tag/03A3>

## Notes
The hypotheses, following the statement from the Stacks project,
may appear surprising: we don't ask that the counit of the adjunction is an isomorphism,
but just that we have some potentially unrelated isomorphism `i : F ⋙ G ≅ 𝟭 C`.

However Lemma A1.1.1 from [Elephant] shows that in this situation the counit itself
must be an isomorphism, and thus that `C` is a reflective subcategory of `D`.

Someone may like to formalize that lemma, and restate this theorem in terms of `Reflective`.
(That lemma has a nice string diagrammatic proof that holds in any bicategory.)
-/

noncomputable section

namespace CategoryTheory

open Limits

universe v₁ v₂ u₁ u₂

namespace AbelianOfAdjunction

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]

variable {D : Type u₂} [Category.{v₂} D] [Abelian D]

variable (F : C ⥤ D)

variable (G : D ⥤ C) [Functor.PreservesZeroMorphisms G]

set_option backward.isDefEq.respectTransparency false in

theorem hasKernels [PreservesFiniteLimits G] (i : F ⋙ G ≅ 𝟭 C) : HasKernels C :=
  { has_limit {X Y} f := by
      have : i.inv.app X ≫ G.map (F.map f) ≫ i.hom.app Y = f := by
        simpa using NatIso.naturality_1 i f
      rw [← this]
      haveI : HasKernel (G.map (F.map f) ≫ i.hom.app _) := Limits.hasKernel_comp_mono _ _
      apply Limits.hasKernel_iso_comp }

set_option backward.isDefEq.respectTransparency false in

theorem hasCokernels (i : F ⋙ G ≅ 𝟭 C) (adj : G ⊣ F) : HasCokernels C :=
  { has_colimit {X Y} f := by
      have : PreservesColimits G := adj.leftAdjoint_preservesColimits
      have : i.inv.app X ≫ G.map (F.map f) ≫ i.hom.app Y = f := by
        simpa using NatIso.naturality_1 i f
      rw [← this]
      haveI : HasCokernel (G.map (F.map f) ≫ i.hom.app _) := Limits.hasCokernel_comp_iso _ _
      apply Limits.hasCokernel_epi_comp }

end AbelianOfAdjunction

open AbelianOfAdjunction
