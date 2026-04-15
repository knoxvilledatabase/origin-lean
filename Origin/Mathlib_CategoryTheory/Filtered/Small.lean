/-
Extracted from CategoryTheory/Filtered/Small.lean
Genuine: 22 of 36 | Dissolved: 0 | Infrastructure: 14
-/
import Origin.Core

/-!
# A functor from a small category to a filtered category factors through a small filtered category

A consequence of this is that if `C` is filtered and finally small, then `C` is also
"finally filtered-small", i.e., there is a final functor from a small filtered category to `C`.
This is occasionally useful, for example in the proof of the recognition theorem for ind-objects
(Proposition 6.1.5 in [Kashiwara2006]).
-/

universe w v v₁ u u₁

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace IsFiltered

section filteredClosure

variable [IsFilteredOrEmpty C] {α : Type w} (f : α → C)

inductive filteredClosure : ObjectProperty C
  | base : (x : α) → filteredClosure (f x)
  | max : {j j' : C} → filteredClosure j → filteredClosure j' → filteredClosure (max j j')
  | coeq : {j j' : C} → filteredClosure j → filteredClosure j' → (f f' : j ⟶ j') →
      filteredClosure (coeq f f')

-- INSTANCE (free from Core): :

namespace FilteredClosureSmall

/-! Our goal for this section is to show that the size of the filtered closure of an `α`-indexed
    family of objects in `C` only depends on the size of `α` and the morphism types of `C`, not on
    the size of the objects of `C`. More precisely, if `α` lives in `Type w`, the objects of `C`
    live in `Type u` and the morphisms of `C` live in `Type v`, then we want
    `Small.{max v w} (FullSubcategory (filteredClosure f))`.

    The strategy is to define a type `AbstractFilteredClosure` which should be an inductive type
    similar to `filteredClosure`, which lives in the correct universe and surjects onto the full
    subcategory. The difficulty with this is that we need to define it at the same time as the map
    `AbstractFilteredClosure → C`, as the coequalizer constructor depends on the actual morphisms
    in `C`. This would require some kind of inductive-recursive definition, which Lean does not
    allow. Our solution is to define a function `ℕ → Σ t : Type (max v w), t → C` by (strong)
    induction and then take the union over all natural numbers, mimicking what one would do in a
    set-theoretic setting. -/

private inductive InductiveStep (n : ℕ) (X : ∀ (k : ℕ), k < n → Σ t : Type (max v w), t → C) :
    Type (max v w)
  | max : {k k' : ℕ} → (hk : k < n) → (hk' : k' < n) → (X _ hk).1 → (X _ hk').1 → InductiveStep n X
  | coeq : {k k' : ℕ} → (hk : k < n) → (hk' : k' < n) → (j : (X _ hk).1) → (j' : (X _ hk').1) →
      ((X _ hk).2 j ⟶ (X _ hk').2 j') → ((X _ hk).2 j ⟶ (X _ hk').2 j') → InductiveStep n X

private noncomputable def inductiveStepRealization (n : ℕ)
    (X : ∀ (k : ℕ), k < n → Σ t : Type (max v w), t → C) : InductiveStep.{w} n X → C
  | (InductiveStep.max hk hk' x y) => max ((X _ hk).2 x) ((X _ hk').2 y)
  | (InductiveStep.coeq _ _ _ _ f g) => coeq f g

private noncomputable def bundledAbstractFilteredClosure :
    ℕ → Σ t : Type (max v w), t → C
  | 0 => ⟨ULift.{v} α, f ∘ ULift.down⟩
  | (n + 1) => ⟨_, inductiveStepRealization (n + 1) (fun m _ => bundledAbstractFilteredClosure m)⟩

private noncomputable def AbstractFilteredClosure : Type (max v w) :=
  Σ n, (bundledAbstractFilteredClosure f n).1

private noncomputable def abstractFilteredClosureRealization : AbstractFilteredClosure f → C :=
  fun x => (bundledAbstractFilteredClosure f x.1).2 x.2

end FilteredClosureSmall

theorem small_fullSubcategory_filteredClosure :
    Small.{max v w} (filteredClosure f).FullSubcategory := by
  refine small_of_injective_of_exists (FilteredClosureSmall.abstractFilteredClosureRealization f)
    (fun _ _ => ObjectProperty.FullSubcategory.ext) ?_
  rintro ⟨j, h⟩
  induction h with
  | base x =>
      refine ⟨⟨0, ?_⟩, ?_⟩
      · #adaptation_note
        /-- On nightly-2025-11-04 we need to add `-implicitDefEqProofs` here. -/
        simp -implicitDefEqProofs only [FilteredClosureSmall.bundledAbstractFilteredClosure]
        exact ULift.up x
      · simp only [FilteredClosureSmall.abstractFilteredClosureRealization]
        rw! [FilteredClosureSmall.bundledAbstractFilteredClosure]
        rfl
  | max hj₁ hj₂ ih ih' =>
    rcases ih with ⟨⟨n, x⟩, rfl⟩
    rcases ih' with ⟨⟨m, y⟩, rfl⟩
    refine ⟨⟨(Max.max n m).succ, ?_⟩, ?_⟩
    · simp only [FilteredClosureSmall.bundledAbstractFilteredClosure]
      refine FilteredClosureSmall.InductiveStep.max ?_ ?_ x y
      all_goals apply Nat.lt_succ_of_le
      exacts [Nat.le_max_left _ _, Nat.le_max_right _ _]
    · simp only [FilteredClosureSmall.abstractFilteredClosureRealization]
      rw! [FilteredClosureSmall.bundledAbstractFilteredClosure]
      rfl
  | coeq hj₁ hj₂ g g' ih ih' =>
    rcases ih with ⟨⟨n, x⟩, rfl⟩
    rcases ih' with ⟨⟨m, y⟩, rfl⟩
    refine ⟨⟨(Max.max n m).succ, ?_⟩, ?_⟩
    · simp only [FilteredClosureSmall.bundledAbstractFilteredClosure]
      refine FilteredClosureSmall.InductiveStep.coeq ?_ ?_ x y g g'
      all_goals apply Nat.lt_succ_of_le
      exacts [Nat.le_max_left _ _, Nat.le_max_right _ _]
    · simp only [FilteredClosureSmall.abstractFilteredClosureRealization]
      rw! [FilteredClosureSmall.bundledAbstractFilteredClosure]
      rfl

-- INSTANCE (free from Core): :

end filteredClosure

variable [IsFilteredOrEmpty C] {D : Type u₁} [Category.{v₁} D] (F : D ⥤ C)

def SmallFilteredIntermediate : Type (max u₁ v) :=
  SmallModel.{max u₁ v} (filteredClosure F.obj).FullSubcategory

-- INSTANCE (free from Core): :

namespace SmallFilteredIntermediate

noncomputable def factoring : D ⥤ SmallFilteredIntermediate F :=
  ObjectProperty.lift _ F filteredClosure.base ⋙ (equivSmallModel _).functor

noncomputable def inclusion : SmallFilteredIntermediate F ⥤ C :=
  (equivSmallModel _).inverse ⋙ ObjectProperty.ι _

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

noncomputable def factoringCompInclusion : factoring F ⋙ inclusion F ≅ F :=
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight (Equivalence.unitIso _).symm _)

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): [Nonempty

end SmallFilteredIntermediate

end

end IsFiltered

namespace IsCofiltered

section cofilteredClosure

variable [IsCofilteredOrEmpty C] {α : Type w} (f : α → C)

inductive cofilteredClosure : ObjectProperty C
  | base : (x : α) → cofilteredClosure (f x)
  | min : {j j' : C} → cofilteredClosure j → cofilteredClosure j' → cofilteredClosure (min j j')
  | eq : {j j' : C} → cofilteredClosure j → cofilteredClosure j' → (f f' : j ⟶ j') →
      cofilteredClosure (eq f f')

-- INSTANCE (free from Core): :

namespace CofilteredClosureSmall

private inductive InductiveStep (n : ℕ) (X : ∀ (k : ℕ), k < n → Σ t : Type (max v w), t → C) :
    Type (max v w)
  | min : {k k' : ℕ} → (hk : k < n) → (hk' : k' < n) → (X _ hk).1 → (X _ hk').1 → InductiveStep n X
  | eq : {k k' : ℕ} → (hk : k < n) → (hk' : k' < n) → (j : (X _ hk).1) → (j' : (X _ hk').1) →
      ((X _ hk).2 j ⟶ (X _ hk').2 j') → ((X _ hk).2 j ⟶ (X _ hk').2 j') → InductiveStep n X

private noncomputable def inductiveStepRealization (n : ℕ)
    (X : ∀ (k : ℕ), k < n → Σ t : Type (max v w), t → C) : InductiveStep.{w} n X → C
  | (InductiveStep.min hk hk' x y) => min ((X _ hk).2 x) ((X _ hk').2 y)
  | (InductiveStep.eq _ _ _ _ f g) => eq f g

private noncomputable def bundledAbstractCofilteredClosure :
    ℕ → Σ t : Type (max v w), t → C
  | 0 => ⟨ULift.{v} α, f ∘ ULift.down⟩
  | (n + 1) => ⟨_, inductiveStepRealization (n + 1) (fun m _ => bundledAbstractCofilteredClosure m)⟩

private noncomputable def AbstractCofilteredClosure : Type (max v w) :=
  Σ n, (bundledAbstractCofilteredClosure f n).1

private noncomputable def abstractCofilteredClosureRealization : AbstractCofilteredClosure f → C :=
  fun x => (bundledAbstractCofilteredClosure f x.1).2 x.2

end CofilteredClosureSmall

theorem small_fullSubcategory_cofilteredClosure :
    Small.{max v w} (cofilteredClosure f).FullSubcategory := by
  refine small_of_injective_of_exists
    (CofilteredClosureSmall.abstractCofilteredClosureRealization f)
    (fun _ _ => ObjectProperty.FullSubcategory.ext) ?_
  rintro ⟨j, h⟩
  induction h with
  | base x =>
    refine ⟨⟨0, ?_⟩,?_⟩
    · #adaptation_note
      /-- On nightly-2025-11-04 we need to add `-implicitDefEqProofs` here. -/
      simp -implicitDefEqProofs only [CofilteredClosureSmall.bundledAbstractCofilteredClosure]
      exact ULift.up x
    · simp only [CofilteredClosureSmall.abstractCofilteredClosureRealization]
      rw! [CofilteredClosureSmall.bundledAbstractCofilteredClosure]
      rfl
  | min hj₁ hj₂ ih ih' =>
    rcases ih with ⟨⟨n, x⟩, rfl⟩
    rcases ih' with ⟨⟨m, y⟩, rfl⟩
    refine ⟨⟨(Max.max n m).succ, ?_⟩, ?_⟩
    · simp only [CofilteredClosureSmall.bundledAbstractCofilteredClosure]
      refine CofilteredClosureSmall.InductiveStep.min ?_ ?_ x y
      all_goals apply Nat.lt_succ_of_le
      exacts [Nat.le_max_left _ _, Nat.le_max_right _ _]
    · simp only [CofilteredClosureSmall.abstractCofilteredClosureRealization]
      rw! [CofilteredClosureSmall.bundledAbstractCofilteredClosure]
      rfl
  | eq hj₁ hj₂ g g' ih ih' =>
    rcases ih with ⟨⟨n, x⟩, rfl⟩
    rcases ih' with ⟨⟨m, y⟩, rfl⟩
    refine ⟨⟨(Max.max n m).succ, ?_⟩, ?_⟩
    · simp only [CofilteredClosureSmall.bundledAbstractCofilteredClosure]
      refine CofilteredClosureSmall.InductiveStep.eq ?_ ?_ x y g g'
      all_goals apply Nat.lt_succ_of_le
      exacts [Nat.le_max_left _ _, Nat.le_max_right _ _]
    · simp only [CofilteredClosureSmall.abstractCofilteredClosureRealization]
      rw! [CofilteredClosureSmall.bundledAbstractCofilteredClosure]
      rfl

-- INSTANCE (free from Core): :

end cofilteredClosure

variable [IsCofilteredOrEmpty C] {D : Type u₁} [Category.{v₁} D] (F : D ⥤ C)

def SmallCofilteredIntermediate : Type (max u₁ v) :=
  SmallModel.{max u₁ v} (cofilteredClosure F.obj).FullSubcategory

-- INSTANCE (free from Core): :

namespace SmallCofilteredIntermediate

noncomputable def factoring : D ⥤ SmallCofilteredIntermediate F :=
  ObjectProperty.lift _ F cofilteredClosure.base ⋙ (equivSmallModel _).functor

noncomputable def inclusion : SmallCofilteredIntermediate F ⥤ C :=
  (equivSmallModel _).inverse ⋙ ObjectProperty.ι _

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

noncomputable def factoringCompInclusion : factoring F ⋙ inclusion F ≅ F :=
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight (Equivalence.unitIso _).symm _)

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): [Nonempty

end SmallCofilteredIntermediate

end

end IsCofiltered

end CategoryTheory
