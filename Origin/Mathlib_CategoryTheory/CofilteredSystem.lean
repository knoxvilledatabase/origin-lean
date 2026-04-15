/-
Extracted from CategoryTheory/CofilteredSystem.lean
Genuine: 10 of 10 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Cofiltered systems

This file deals with properties of cofiltered (and inverse) systems.

## Main definitions

Given a functor `F : J ⥤ Type v`:

* For `j : J`, `F.eventualRange j` is the intersection of all ranges of morphisms `F.map f`
  where `f` has codomain `j`.
* `F.IsMittagLeffler` states that the functor `F` satisfies the Mittag-Leffler
  condition: the ranges of morphisms `F.map f` (with `f` having codomain `j`) stabilize.
* If `J` is cofiltered `F.toEventualRanges` is the subfunctor of `F` obtained by restriction
  to `F.eventualRange`.
* `F.toPreimages` restricts a functor to preimages of a given set in some `F.obj i`. If `J` is
  cofiltered, then it is Mittag-Leffler if `F` is, see `IsMittagLeffler.toPreimages`.

## Main statements

* `nonempty_sections_of_finite_cofiltered_system` shows that if `J` is cofiltered and each
  `F.obj j` is nonempty and finite, `F.sections` is nonempty.
* `nonempty_sections_of_finite_inverse_system` is a specialization of the above to `J` being a
  directed set (and `F : Jᵒᵖ ⥤ Type v`).
* `isMittagLeffler_of_exists_finite_range` shows that if `J` is cofiltered and for all `j`,
  there exists some `i` and `f : i ⟶ j` such that the range of `F.map f` is finite, then
  `F` is Mittag-Leffler.
* `surjective_toEventualRanges` shows that if `F` is Mittag-Leffler, then `F.toEventualRanges`
  has all morphisms `F.map f` surjective.

## TODO

* Prove [Stacks: Lemma 0597](https://stacks.math.columbia.edu/tag/0597)

## References

* [Stacks: Mittag-Leffler systems](https://stacks.math.columbia.edu/tag/0594)

## Tags

Mittag-Leffler, surjective, eventual range, inverse system,

-/

universe u v w

open CategoryTheory CategoryTheory.IsCofiltered Set CategoryTheory.FunctorToTypes

section FiniteKonig

theorem nonempty_sections_of_finite_cofiltered_system.init {J : Type u} [SmallCategory J]
    [IsCofilteredOrEmpty J] (F : J ⥤ Type u) [hf : ∀ j, Finite (F.obj j)]
    [hne : ∀ j, Nonempty (F.obj j)] : F.sections.Nonempty := by
  let F' : J ⥤ TopCat := F ⋙ TopCat.discrete
  haveI : ∀ j, DiscreteTopology (F'.obj j) := fun _ => ⟨rfl⟩
  haveI : ∀ j, Finite (F'.obj j) := hf
  haveI : ∀ j, Nonempty (F'.obj j) := hne
  obtain ⟨⟨u, hu⟩⟩ := TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system.{u} F'
  exact ⟨u, hu⟩

theorem nonempty_sections_of_finite_cofiltered_system {J : Type u} [Category.{w} J]
    [IsCofilteredOrEmpty J] (F : J ⥤ Type v) [∀ j : J, Finite (F.obj j)]
    [∀ j : J, Nonempty (F.obj j)] : F.sections.Nonempty := by
  -- Step 1: lift everything to the `max u v w` universe.
  let J' : Type max w v u := AsSmall.{max w v} J
  let down : J' ⥤ J := AsSmall.down
  let F' : J' ⥤ Type (max u v w) := down ⋙ F ⋙ uliftFunctor.{max u w, v}
  haveI : ∀ i, Nonempty (F'.obj i) := fun i => ⟨⟨Classical.arbitrary (F.obj (down.obj i))⟩⟩
  haveI : ∀ i, Finite (F'.obj i) := fun i => Finite.of_equiv (F.obj (down.obj i)) Equiv.ulift.symm
  -- Step 2: apply the bootstrap theorem
  cases isEmpty_or_nonempty J
  · fconstructor <;> apply isEmptyElim
  haveI : IsCofiltered J := ⟨⟩
  obtain ⟨u, hu⟩ := nonempty_sections_of_finite_cofiltered_system.init F'
  -- Step 3: interpret the results
  use fun j => (u ⟨j⟩).down
  intro j j' f
  have h := @hu (⟨j⟩ : J') (⟨j'⟩ : J') (ULift.up f)
  simp only [F', down, AsSmall.down, Functor.comp_map, uliftFunctor_map] at h
  simp_rw [← h]
  rfl

theorem nonempty_sections_of_finite_inverse_system {J : Type u} [Preorder J] [IsDirectedOrder J]
    (F : Jᵒᵖ ⥤ Type v) [∀ j : Jᵒᵖ, Finite (F.obj j)] [∀ j : Jᵒᵖ, Nonempty (F.obj j)] :
    F.sections.Nonempty := nonempty_sections_of_finite_cofiltered_system F

end FiniteKonig

namespace CategoryTheory

namespace Functor

variable {J : Type u} [Category* J] (F : J ⥤ Type v) {i j k : J} (s : Set (F.obj i))

def eventualRange (j : J) :=
  ⋂ (i) (f : i ⟶ j), range (F.map f)

theorem mem_eventualRange_iff {x : F.obj j} :
    x ∈ F.eventualRange j ↔ ∀ ⦃i⦄ (f : i ⟶ j), x ∈ range (F.map f) :=
  mem_iInter₂

def IsMittagLeffler : Prop :=
  ∀ j : J, ∃ (i : _) (f : i ⟶ j), ∀ ⦃k⦄ (g : k ⟶ j), range (F.map f) ⊆ range (F.map g)

theorem isMittagLeffler_iff_eventualRange :
    F.IsMittagLeffler ↔ ∀ j : J, ∃ (i : _) (f : i ⟶ j), F.eventualRange j = range (F.map f) :=
  forall_congr' fun _ =>
    exists₂_congr fun _ _ =>
      ⟨fun h => (iInter₂_subset _ _).antisymm <| subset_iInter₂ h, fun h => h ▸ iInter₂_subset⟩

theorem IsMittagLeffler.subset_image_eventualRange (h : F.IsMittagLeffler) (f : j ⟶ i) :
    F.eventualRange i ⊆ F.map f '' F.eventualRange j := by
  obtain ⟨k, g, hg⟩ := F.isMittagLeffler_iff_eventualRange.1 h j
  rw [hg]; intro x hx
  obtain ⟨x, rfl⟩ := F.mem_eventualRange_iff.1 hx (g ≫ f)
  exact ⟨_, ⟨x, rfl⟩, by rw [map_comp, comp_apply]⟩

theorem eventualRange_eq_range_precomp (f : i ⟶ j) (g : j ⟶ k)
    (h : F.eventualRange k = range (F.map g)) : F.eventualRange k = range (F.map <| f ≫ g) := by
  apply subset_antisymm
  · apply iInter₂_subset
  · rw [h, F.map_comp, types_comp]
    apply range_comp_subset_range

theorem isMittagLeffler_of_surjective (h : ∀ ⦃i j : J⦄ (f : i ⟶ j), Function.Surjective (F.map f)) :
    F.IsMittagLeffler :=
  fun j => ⟨j, 𝟙 j, fun k g => by rw [map_id, types_id, range_id, (h g).range_eq]⟩
