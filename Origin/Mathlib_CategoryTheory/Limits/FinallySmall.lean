/-
Extracted from CategoryTheory/Limits/FinallySmall.lean
Genuine: 22 of 33 | Dissolved: 0 | Infrastructure: 11
-/
import Origin.Core

/-!
# Finally small categories

A category given by `(J : Type u) [Category.{v} J]` is `w`-finally small if there exists a
`FinalModel J : Type w` equipped with `[SmallCategory (FinalModel J)]` and a final functor
`FinalModel J ⥤ J`.

This means that if a category `C` has colimits of size `w` and `J` is `w`-finally small, then
`C` has colimits of shape `J`. In this way, the notion of "finally small" can be seen as a
generalization of the notion of "essentially small" for indexing categories of colimits.

Dually, we have a notion of initially small category.

We show that a finally small category admits a small weakly terminal set, i.e., a small set `s` of
objects such that from every object there is a morphism to a member of `s`. We also show that the
converse holds if `J` is filtered.
-/

universe w w' v v₁ u u₁

open CategoryTheory Functor

namespace CategoryTheory

section FinallySmall

variable (J : Type u) [Category.{v} J]

class FinallySmall : Prop where
  /-- There is a final functor from a small category. -/
  final_smallCategory : ∃ (S : Type w) (_ : SmallCategory S) (F : S ⥤ J), Final F

theorem FinallySmall.mk' {J : Type u} [Category.{v} J] {S : Type w} [SmallCategory S]
    (F : S ⥤ J) [Final F] : FinallySmall.{w} J :=
  ⟨S, _, F, inferInstance⟩

def FinalModel [FinallySmall.{w} J] : Type w :=
  Classical.choose (@FinallySmall.final_smallCategory J _ _)

-- INSTANCE (free from Core): smallCategoryFinalModel

noncomputable def fromFinalModel [FinallySmall.{w} J] : FinalModel J ⥤ J :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec
    (@FinallySmall.final_smallCategory J _ _)))

-- INSTANCE (free from Core): final_fromFinalModel

theorem finallySmall_of_essentiallySmall [EssentiallySmall.{w} J] : FinallySmall.{w} J :=
  FinallySmall.mk' (equivSmallModel.{w} J).inverse

variable {J}

variable {K : Type u₁} [Category.{v₁} K]

theorem finallySmall_of_final_of_finallySmall [FinallySmall.{w} K] (F : K ⥤ J) [Final F] :
    FinallySmall.{w} J :=
  suffices Final ((fromFinalModel K) ⋙ F) from .mk' ((fromFinalModel K) ⋙ F)
  final_comp _ _

theorem finallySmall_of_final_of_essentiallySmall [EssentiallySmall.{w} K] (F : K ⥤ J) [Final F] :
    FinallySmall.{w} J :=
  have := finallySmall_of_essentiallySmall K
  finallySmall_of_final_of_finallySmall F

-- INSTANCE (free from Core): [Limits.HasTerminal

-- INSTANCE (free from Core): {J'

end FinallySmall

section InitiallySmall

variable (J : Type u) [Category.{v} J]

class InitiallySmall : Prop where
  /-- There is an initial functor from a small category. -/
  initial_smallCategory : ∃ (S : Type w) (_ : SmallCategory S) (F : S ⥤ J), Initial F

theorem InitiallySmall.mk' {J : Type u} [Category.{v} J] {S : Type w} [SmallCategory S]
    (F : S ⥤ J) [Initial F] : InitiallySmall.{w} J :=
  ⟨S, _, F, inferInstance⟩

def InitialModel [InitiallySmall.{w} J] : Type w :=
  Classical.choose (@InitiallySmall.initial_smallCategory J _ _)

-- INSTANCE (free from Core): smallCategoryInitialModel

noncomputable def fromInitialModel [InitiallySmall.{w} J] : InitialModel J ⥤ J :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec
    (@InitiallySmall.initial_smallCategory J _ _)))

-- INSTANCE (free from Core): initial_fromInitialModel

theorem initiallySmall_of_essentiallySmall [EssentiallySmall.{w} J] : InitiallySmall.{w} J :=
  InitiallySmall.mk' (equivSmallModel.{w} J).inverse

variable {J}

variable {K : Type u₁} [Category.{v₁} K]

theorem initiallySmall_of_initial_of_initiallySmall [InitiallySmall.{w} K]
    (F : K ⥤ J) [Initial F] : InitiallySmall.{w} J :=
  suffices Initial ((fromInitialModel K) ⋙ F) from .mk' ((fromInitialModel K) ⋙ F)
  initial_comp _ _

theorem initiallySmall_of_initial_of_essentiallySmall [EssentiallySmall.{w} K]
    (F : K ⥤ J) [Initial F] : InitiallySmall.{w} J :=
  have := initiallySmall_of_essentiallySmall K
  initiallySmall_of_initial_of_initiallySmall F

-- INSTANCE (free from Core): [Limits.HasInitial

-- INSTANCE (free from Core): [LocallySmall.{w}

-- INSTANCE (free from Core): {J'

end InitiallySmall

-- INSTANCE (free from Core): {J

-- INSTANCE (free from Core): {J

section WeaklyTerminal

variable (J : Type u) [Category.{v} J]

theorem FinallySmall.exists_small_weakly_terminal_set [FinallySmall.{w} J] :
    ∃ (s : Set J) (_ : Small.{w} s), ∀ i, ∃ j ∈ s, Nonempty (i ⟶ j) := by
  refine ⟨Set.range (fromFinalModel J).obj, inferInstance, fun i => ?_⟩
  obtain ⟨f⟩ : Nonempty (StructuredArrow i (fromFinalModel J)) := IsConnected.is_nonempty
  exact ⟨(fromFinalModel J).obj f.right, Set.mem_range_self _, ⟨f.hom⟩⟩

variable {J} in

theorem finallySmall_of_small_weakly_terminal_set [IsFilteredOrEmpty J] (s : Set J) [Small.{v} s]
    (hs : ∀ i, ∃ j ∈ s, Nonempty (i ⟶ j)) : FinallySmall.{v} J := by
  suffices Functor.Final (ObjectProperty.ι (· ∈ s)) from
    finallySmall_of_final_of_essentiallySmall (ObjectProperty.ι (· ∈ s))
  refine Functor.final_of_exists_of_isFiltered_of_fullyFaithful _ (fun i => ?_)
  obtain ⟨j, hj₁, hj₂⟩ := hs i
  exact ⟨⟨j, hj₁⟩, hj₂⟩

theorem finallySmall_iff_exists_small_weakly_terminal_set [IsFilteredOrEmpty J] :
    FinallySmall.{v} J ↔ ∃ (s : Set J) (_ : Small.{v} s), ∀ i, ∃ j ∈ s, Nonempty (i ⟶ j) := by
  refine ⟨fun _ => FinallySmall.exists_small_weakly_terminal_set _, fun h => ?_⟩
  rcases h with ⟨s, hs, hs'⟩
  exact finallySmall_of_small_weakly_terminal_set s hs'

end WeaklyTerminal

section WeaklyInitial

variable (J : Type u) [Category.{v} J]

theorem InitiallySmall.exists_small_weakly_initial_set [InitiallySmall.{w} J] :
    ∃ (s : Set J) (_ : Small.{w} s), ∀ i, ∃ j ∈ s, Nonempty (j ⟶ i) := by
  refine ⟨Set.range (fromInitialModel J).obj, inferInstance, fun i => ?_⟩
  obtain ⟨f⟩ : Nonempty (CostructuredArrow (fromInitialModel J) i) := IsConnected.is_nonempty
  exact ⟨(fromInitialModel J).obj f.left, Set.mem_range_self _, ⟨f.hom⟩⟩

variable {J} in

theorem initiallySmall_of_small_weakly_initial_set [IsCofilteredOrEmpty J] (s : Set J) [Small.{v} s]
    (hs : ∀ i, ∃ j ∈ s, Nonempty (j ⟶ i)) : InitiallySmall.{v} J := by
  suffices Functor.Initial (ObjectProperty.ι (· ∈ s)) from
    initiallySmall_of_initial_of_essentiallySmall (ObjectProperty.ι (· ∈ s))
  refine Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful _ (fun i => ?_)
  obtain ⟨j, hj₁, hj₂⟩ := hs i
  exact ⟨⟨j, hj₁⟩, hj₂⟩

theorem initiallySmall_iff_exists_small_weakly_initial_set [IsCofilteredOrEmpty J] :
    InitiallySmall.{v} J ↔ ∃ (s : Set J) (_ : Small.{v} s), ∀ i, ∃ j ∈ s, Nonempty (j ⟶ i) := by
  refine ⟨fun _ => InitiallySmall.exists_small_weakly_initial_set _, fun h => ?_⟩
  rcases h with ⟨s, hs, hs'⟩
  exact initiallySmall_of_small_weakly_initial_set s hs'

end WeaklyInitial

namespace Limits

theorem hasColimitsOfShape_of_finallySmall (J : Type u) [Category.{v} J] [FinallySmall.{w} J]
    (C : Type u₁) [Category.{v₁} C] [HasColimitsOfSize.{w, w} C] : HasColimitsOfShape J C :=
  Final.hasColimitsOfShape_of_final (fromFinalModel J)

theorem hasLimitsOfShape_of_initiallySmall (J : Type u) [Category.{v} J] [InitiallySmall.{w} J]
    (C : Type u₁) [Category.{v₁} C] [HasLimitsOfSize.{w, w} C] : HasLimitsOfShape J C :=
  Initial.hasLimitsOfShape_of_initial (fromInitialModel J)

end Limits

end CategoryTheory
