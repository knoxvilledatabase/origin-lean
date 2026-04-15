/-
Extracted from Topology/Category/TopCat/Limits/Konig.lean
Genuine: 7 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.Topology.Category.TopCat.Limits.Basic

/-!
# Topological Kőnig's lemma

A topological version of Kőnig's lemma is that the inverse limit of nonempty compact Hausdorff
spaces is nonempty.  (Note: this can be generalized further to inverse limits of nonempty compact
T0 spaces, where all the maps are closed maps; see [Stone1979] --- however there is an erratum
for Theorem 4 that the element in the inverse limit can have cofinally many components that are
not closed points.)

We give this in a more general form, which is that cofiltered limits
of nonempty compact Hausdorff spaces are nonempty
(`nonempty_limitCone_of_compact_t2_cofiltered_system`).

This also applies to inverse limits, where `{J : Type u} [Preorder J] [IsDirected J (≤)]` and
`F : Jᵒᵖ ⥤ TopCat`.

The theorem is specialized to nonempty finite types (which are compact Hausdorff with the
discrete topology) in lemmas `nonempty_sections_of_finite_cofiltered_system` and
`nonempty_sections_of_finite_inverse_system` in the file `Mathlib.CategoryTheory.CofilteredSystem`.

(See <https://stacks.math.columbia.edu/tag/086J> for the Set version.)
-/

open CategoryTheory

open CategoryTheory.Limits

universe v u w

noncomputable section

namespace TopCat

section TopologicalKonig

variable {J : Type u} [SmallCategory J]

variable (F : J ⥤ TopCat.{v})

private abbrev FiniteDiagramArrow {J : Type u} [SmallCategory J] (G : Finset J) :=
  Σ' (X Y : J) (_ : X ∈ G) (_ : Y ∈ G), X ⟶ Y

private abbrev FiniteDiagram (J : Type u) [SmallCategory J] :=
  Σ G : Finset J, Finset (FiniteDiagramArrow G)

def partialSections {J : Type u} [SmallCategory J] (F : J ⥤ TopCat.{v}) {G : Finset J}
    (H : Finset (FiniteDiagramArrow G)) : Set (∀ j, F.obj j) :=
  {u | ∀ {f : FiniteDiagramArrow G} (_ : f ∈ H), F.map f.2.2.2.2 (u f.1) = u f.2.1}

theorem partialSections.nonempty [IsCofilteredOrEmpty J] [h : ∀ j : J, Nonempty (F.obj j)]
    {G : Finset J} (H : Finset (FiniteDiagramArrow G)) : (partialSections F H).Nonempty := by
  classical
  cases isEmpty_or_nonempty J
  · exact ⟨isEmptyElim, fun {j} => IsEmpty.elim' inferInstance j.1⟩
  haveI : IsCofiltered J := ⟨⟩
  use fun j : J =>
    if hj : j ∈ G then F.map (IsCofiltered.infTo G H hj) (h (IsCofiltered.inf G H)).some
    else (h _).some
  rintro ⟨X, Y, hX, hY, f⟩ hf
  dsimp only
  rwa [dif_pos hX, dif_pos hY, ← comp_app, ← F.map_comp, @IsCofiltered.infTo_commutes _ _ _ G H]

theorem partialSections.directed :
    Directed Superset fun G : FiniteDiagram J => partialSections F G.2 := by
  classical
  intro A B
  let ιA : FiniteDiagramArrow A.1 → FiniteDiagramArrow (A.1 ⊔ B.1) := fun f =>
    ⟨f.1, f.2.1, Finset.mem_union_left _ f.2.2.1, Finset.mem_union_left _ f.2.2.2.1, f.2.2.2.2⟩
  let ιB : FiniteDiagramArrow B.1 → FiniteDiagramArrow (A.1 ⊔ B.1) := fun f =>
    ⟨f.1, f.2.1, Finset.mem_union_right _ f.2.2.1, Finset.mem_union_right _ f.2.2.2.1, f.2.2.2.2⟩
  refine ⟨⟨A.1 ⊔ B.1, A.2.image ιA ⊔ B.2.image ιB⟩, ?_, ?_⟩
  · rintro u hu f hf
    have : ιA f ∈ A.2.image ιA ⊔ B.2.image ιB := by
      apply Finset.mem_union_left
      rw [Finset.mem_image]
      exact ⟨f, hf, rfl⟩
    exact hu this
  · rintro u hu f hf
    have : ιB f ∈ A.2.image ιA ⊔ B.2.image ιB := by
      apply Finset.mem_union_right
      rw [Finset.mem_image]
      exact ⟨f, hf, rfl⟩
    exact hu this

theorem partialSections.closed [∀ j : J, T2Space (F.obj j)] {G : Finset J}
    (H : Finset (FiniteDiagramArrow G)) : IsClosed (partialSections F H) := by
  have :
    partialSections F H =
      ⋂ (f : FiniteDiagramArrow G) (_ : f ∈ H), {u | F.map f.2.2.2.2 (u f.1) = u f.2.1} := by
    ext1
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    rfl
  rw [this]
  apply isClosed_biInter
  intro f _
  -- Porting note: can't see through forget
  have : T2Space ((forget TopCat).obj (F.obj f.snd.fst)) :=
    inferInstanceAs (T2Space (F.obj f.snd.fst))
  apply isClosed_eq
  -- Porting note: used to be a single `continuity` that closed both goals
  · exact (F.map f.snd.snd.snd.snd).continuous.comp (continuous_apply f.fst)
  · continuity

theorem nonempty_limitCone_of_compact_t2_cofiltered_system (F : J ⥤ TopCat.{max v u})
    [IsCofilteredOrEmpty J]
    [∀ j : J, Nonempty (F.obj j)] [∀ j : J, CompactSpace (F.obj j)] [∀ j : J, T2Space (F.obj j)] :
    Nonempty (TopCat.limitCone F).pt := by
  classical
  obtain ⟨u, hu⟩ :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed (fun G => partialSections F _)
      (partialSections.directed F) (fun G => partialSections.nonempty F _)
      (fun G => IsClosed.isCompact (partialSections.closed F _)) fun G =>
      partialSections.closed F _
  use u
  intro X Y f
  let G : FiniteDiagram J :=
    ⟨{X, Y},
      {⟨X, Y, by simp only [true_or, eq_self_iff_true, Finset.mem_insert], by
          simp only [eq_self_iff_true, or_true, Finset.mem_insert, Finset.mem_singleton], f⟩}⟩
  exact hu _ ⟨G, rfl⟩ (Finset.mem_singleton_self _)

end TopologicalKonig

end TopCat
