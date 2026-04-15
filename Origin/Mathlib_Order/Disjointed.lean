/-
Extracted from Order/Disjointed.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Making a sequence disjoint

This file defines the way to make a sequence of sets - or, more generally, a map from a partially
ordered type `ι` into a (generalized) Boolean algebra `α` - into a *pairwise disjoint* sequence with
the same partial sups.

For a sequence `f : ℕ → α`, this new sequence will be `f 0`, `f 1 \ f 0`, `f 2 \ (f 0 ⊔ f 1) ⋯`.
It is actually unique, as `disjointed_unique` shows.

## Main declarations

* `disjointed f`: The map sending `i` to `f i \ (⨆ j < i, f j)`. We require the index type to be a
  `LocallyFiniteOrderBot` to ensure that the supremum is well defined.
* `partialSups_disjointed`: `disjointed f` has the same partial sups as `f`.
* `disjoint_disjointed`: The elements of `disjointed f` are pairwise disjoint.
* `disjointed_unique`: `disjointed f` is the only pairwise disjoint sequence having the same partial
  sups as `f`.
* `Fintype.sup_disjointed` (for finite `ι`) or `iSup_disjointed` (for complete `α`):
  `disjointed f` has the same supremum as `f`. Limiting case of `partialSups_disjointed`.
* `Fintype.exists_disjointed_le`: for any finite family `f : ι → α`, there exists a pairwise
  disjoint family `g : ι → α` which is bounded above by `f` and has the same supremum. This is
  an analogue of `disjointed` for arbitrary finite index types (but without any uniqueness).

We also provide set notation variants of some lemmas.
-/

assert_not_exists SuccAddOrder

open Finset Order

variable {α ι : Type*}

open scoped Function -- required for scoped `on` notation

section GeneralizedBooleanAlgebra

variable [GeneralizedBooleanAlgebra α]

section Preorder -- the *index type* is a preorder

variable [Preorder ι] [LocallyFiniteOrderBot ι]

def disjointed (f : ι → α) (i : ι) : α := f i \ (Iio i).sup f

lemma disjointed_of_isMin (f : ι → α) {i : ι} (hn : IsMin i) :
    disjointed f i = f i := by
  have : Iio i = ∅ := by rwa [← Finset.coe_eq_empty, coe_Iio, Set.Iio_eq_empty_iff]
  simp only [disjointed_apply, this, sup_empty, sdiff_bot]
