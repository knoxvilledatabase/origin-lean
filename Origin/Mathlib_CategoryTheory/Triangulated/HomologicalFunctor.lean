/-
Extracted from CategoryTheory/Triangulated/HomologicalFunctor.lean
Genuine: 8 of 13 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-! # Homological functors

In this file, given a functor `F : C ⥤ A` from a pretriangulated category to
an abelian category, we define the type class `F.IsHomological`, which is the property
that `F` sends distinguished triangles in `C` to exact sequences in `A`.

If `F` has been endowed with `[F.ShiftSequence ℤ]`, then we may think
of the functor `F` as a `H^0`, and then the `H^n` functors are the functors `F.shift n : C ⥤ A`:
we have isomorphisms `(F.shift n).obj X ≅ F.obj (X⟦n⟧)`, but through the choice of this
"shift sequence", the user may provide functors with better definitional properties.

Given a triangle `T` in `C`, we define a connecting homomorphism
`F.homologySequenceδ T n₀ n₁ h : (F.shift n₀).obj T.obj₃ ⟶ (F.shift n₁).obj T.obj₁`
under the assumption `h : n₀ + 1 = n₁`. When `T` is distinguished, this connecting
homomorphism is part of a long exact sequence
`... ⟶ (F.shift n₀).obj T.obj₁ ⟶ (F.shift n₀).obj T.obj₂ ⟶ (F.shift n₀).obj T.obj₃ ⟶ ...`

The exactness of this long exact sequence is given by three lemmas
`F.homologySequence_exact₁`, `F.homologySequence_exact₂` and `F.homologySequence_exact₃`.

If `F` is a homological functor, we define the strictly full triangulated subcategory
`F.homologicalKernel`: it consists of objects `X : C` such that for all `n : ℤ`,
`(F.shift n).obj X` (or `F.obj (X⟦n⟧)`) is zero. We show that a morphism `f` in `C`
belongs to `F.homologicalKernel.trW` (i.e. the cone of `f` is in this kernel) iff
`(F.shift n).map f` is an isomorphism for all `n : ℤ`.

Note: depending on the sources, homological functors are sometimes
called cohomological functors, while certain authors use "cohomological functors"
for "contravariant" functors (i.e. functors `Cᵒᵖ ⥤ A`).

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*][verdier1996]

-/

namespace CategoryTheory

open Category Limits Pretriangulated ZeroObject Preadditive

variable {C D A : Type*} [Category* C] [HasShift C ℤ]
  [Category* D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ (n : ℤ), (CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D]
  [Category* A]

namespace Functor

variable (F : C ⥤ A)

def homologicalKernel : ObjectProperty C :=
  fun X ↦ ∀ (n : ℤ), IsZero (F.obj (X⟦n⟧))

lemma mem_homologicalKernel_iff [F.ShiftSequence ℤ] (X : C) :
    F.homologicalKernel X ↔ ∀ (n : ℤ), IsZero ((F.shift n).obj X) := by
  simp only [← fun (n : ℤ) => Iso.isZero_iff ((F.isoShift n).app X),
    homologicalKernel, comp_obj]

section Pretriangulated

variable [HasZeroObject C] [Preadditive C] [∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive]
  [Pretriangulated C] [Abelian A]

class IsHomological : Prop extends F.PreservesZeroMorphisms where
  exact (T : Triangle C) (hT : T ∈ distTriang C) :
    ((shortComplexOfDistTriangle T hT).map F).Exact

lemma map_distinguished_exact [F.IsHomological] (T : Triangle C) (hT : T ∈ distTriang C) :
    ((shortComplexOfDistTriangle T hT).map F).Exact :=
  IsHomological.exact _ hT

-- INSTANCE (free from Core): (L

lemma IsHomological.mk' [F.PreservesZeroMorphisms]
    (hF : ∀ (T : Pretriangulated.Triangle C) (hT : T ∈ distTriang C),
      ∃ (T' : Pretriangulated.Triangle C) (e : T ≅ T'),
      ((shortComplexOfDistTriangle T' (isomorphic_distinguished _ hT _ e.symm)).map F).Exact) :
    F.IsHomological where
  exact T hT := by
    obtain ⟨T', e, h'⟩ := hF T hT
    exact (ShortComplex.exact_iff_of_iso
      (F.mapShortComplex.mapIso ((shortComplexOfDistTriangleIsoOfIso e hT)))).2 h'

lemma IsHomological.of_iso {F₁ F₂ : C ⥤ A} [F₁.IsHomological] (e : F₁ ≅ F₂) :
    F₂.IsHomological :=
  have := preservesZeroMorphisms_of_iso e
  ⟨fun T hT => ShortComplex.exact_of_iso (ShortComplex.mapNatIso _ e)
    (F₁.map_distinguished_exact T hT)⟩

variable [F.IsHomological]

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

end

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

lemma isHomological_of_localization (L : C ⥤ D)
    [L.CommShift ℤ] [L.IsTriangulated] [L.mapArrow.EssSurj] (F : D ⥤ A)
    (G : C ⥤ A) (e : L ⋙ F ≅ G) [G.IsHomological] :
    F.IsHomological := by
  have : F.PreservesZeroMorphisms := preservesZeroMorphisms_of_map_zero_object
    (F.mapIso L.mapZeroObject.symm ≪≫ e.app _ ≪≫ G.mapZeroObject)
  have : (L ⋙ F).IsHomological := IsHomological.of_iso e.symm
  refine IsHomological.mk' _ (fun T hT => ?_)
  rw [L.distTriang_iff] at hT
  obtain ⟨T₀, e, hT₀⟩ := hT
  exact ⟨L.mapTriangle.obj T₀, e, (L ⋙ F).map_distinguished_exact _ hT₀⟩

end Pretriangulated

noncomputable def homologySequenceδ
    [F.ShiftSequence ℤ] (T : Triangle C) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (F.shift n₀).obj T.obj₃ ⟶ (F.shift n₁).obj T.obj₁ :=
  F.shiftMap T.mor₃ n₀ n₁ (by rw [add_comm 1, h])

variable {T T'}
