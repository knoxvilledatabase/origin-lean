/-
Extracted from CategoryTheory/Limits/Shapes/Countable.lean
Genuine: 12 of 28 | Dissolved: 0 | Infrastructure: 16
-/
import Origin.Core

/-!
# Countable limits and colimits

A typeclass for categories with all countable (co)limits.

We also prove that all cofiltered limits over countable preorders are isomorphic to sequential
limits, see `sequentialFunctor_initial`.

## Projects

* There is a series of `proof_wanted` at the bottom of this file, implying that all cofiltered
  limits over countable categories are isomorphic to sequential limits.

* Prove the dual result for filtered colimits.

-/

open CategoryTheory Opposite CountableCategory

variable (C : Type*) [Category* C] (J : Type*) [Countable J]

namespace CategoryTheory.Limits

class HasCountableLimits : Prop where
  /-- `C` has all limits over any type `J` whose objects and morphisms lie in the same universe
  and which has countably many objects and morphisms -/
  out (J : Type) [SmallCategory J] [CountableCategory J] : HasLimitsOfShape J C := by infer_instance

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

universe v in

-- INSTANCE (free from Core): [HasCountableLimits

class HasCountableProducts where
  out (J : Type) [Countable J] : HasProductsOfShape J C

-- INSTANCE (free from Core): [HasCountableProducts

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

class HasCountableColimits : Prop where
  /-- `C` has all limits over any type `J` whose objects and morphisms lie in the same universe
  and which has countably many objects and morphisms -/
  out (J : Type) [SmallCategory J] [CountableCategory J] : HasColimitsOfShape J C

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

universe v in

-- INSTANCE (free from Core): [HasCountableColimits

class HasCountableCoproducts where
  out (J : Type) [Countable J] : HasCoproductsOfShape J C

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): [HasCountableCoproducts

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

section Preorder

namespace IsFiltered

attribute [local instance] IsFiltered.nonempty

variable {C} [Preorder J] [IsFiltered J]

noncomputable def sequentialFunctor_obj : ℕ → J := fun
  | .zero => (exists_surjective_nat _).choose 0
  | .succ n => (IsFilteredOrEmpty.cocone_objs ((exists_surjective_nat _).choose n)
      (sequentialFunctor_obj n)).choose

theorem sequentialFunctor_map : Monotone (sequentialFunctor_obj J) :=
  monotone_nat_of_le_succ fun n ↦
    leOfHom (IsFilteredOrEmpty.cocone_objs ((exists_surjective_nat _).choose n)
      (sequentialFunctor_obj J n)).choose_spec.choose_spec.choose

noncomputable def sequentialFunctor : ℕ ⥤ J where
  obj n := sequentialFunctor_obj J n
  map h := homOfLE (sequentialFunctor_map J (leOfHom h))

theorem sequentialFunctor_final_aux (j : J) : ∃ (n : ℕ), j ≤ sequentialFunctor_obj J n := by
  obtain ⟨m, h⟩ := (exists_surjective_nat _).choose_spec j
  refine ⟨m + 1, ?_⟩
  simpa only [h] using leOfHom (IsFilteredOrEmpty.cocone_objs ((exists_surjective_nat _).choose m)
    (sequentialFunctor_obj J m)).choose_spec.choose

-- INSTANCE (free from Core): sequentialFunctor_final

end IsFiltered

namespace IsCofiltered

attribute [local instance] IsCofiltered.nonempty

variable {C} [Preorder J] [IsCofiltered J]

noncomputable def sequentialFunctor_obj : ℕ → J := fun
  | .zero => (exists_surjective_nat _).choose 0
  | .succ n => (IsCofilteredOrEmpty.cone_objs ((exists_surjective_nat _).choose n)
      (sequentialFunctor_obj n)).choose

theorem sequentialFunctor_map : Antitone (sequentialFunctor_obj J) :=
  antitone_nat_of_succ_le fun n ↦
    leOfHom (IsCofilteredOrEmpty.cone_objs ((exists_surjective_nat _).choose n)
      (sequentialFunctor_obj J n)).choose_spec.choose_spec.choose

noncomputable def sequentialFunctor : ℕᵒᵖ ⥤ J where
  obj n := sequentialFunctor_obj J (unop n)
  map h := homOfLE (sequentialFunctor_map J (leOfHom h.unop))

theorem sequentialFunctor_initial_aux (j : J) : ∃ (n : ℕ), sequentialFunctor_obj J n ≤ j := by
  obtain ⟨m, h⟩ := (exists_surjective_nat _).choose_spec j
  refine ⟨m + 1, ?_⟩
  simpa only [h] using leOfHom (IsCofilteredOrEmpty.cone_objs ((exists_surjective_nat _).choose m)
    (sequentialFunctor_obj J m)).choose_spec.choose

-- INSTANCE (free from Core): sequentialFunctor_initial
