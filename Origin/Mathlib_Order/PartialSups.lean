/-
Extracted from Order/PartialSups.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The monotone sequence of partial supremums of a sequence

For `ι` a preorder in which all bounded-above intervals are finite (such as `ℕ`), and `α` a
`⊔`-semilattice, we define `partialSups : (ι → α) → ι →o α` by the formula
`partialSups f i = (Finset.Iic i).sup' ⋯ f`, where the `⋯` denotes a proof that `Finset.Iic i` is
nonempty. This is a way of spelling `⊔ k ≤ i, f k` which does not require a `α` to have a bottom
element, and makes sense in conditionally-complete lattices (where indexed suprema over sets are
badly-behaved).

Under stronger hypotheses on `α` and `ι`, we show that this coincides with other candidate
definitions, see e.g. `partialSups_eq_biSup`, `partialSups_eq_sup_range`,
and `partialSups_eq_sup'_range`.

We show this construction gives a Galois insertion between functions `ι → α` and monotone functions
`ι →o α`, see `partialSups.gi`.

## Notes

One might dispute whether this sequence should start at `f 0` or `⊥`. We choose the former because:
* Starting at `⊥` requires... having a bottom element.
* `fun f i ↦ (Finset.Iio i).sup f` is already effectively the sequence starting at `⊥`.
* If we started at `⊥` we wouldn't have the Galois insertion. See `partialSups.gi`.

-/

open Finset

variable {α β ι : Type*}

section SemilatticeSup

variable [SemilatticeSup α] [SemilatticeSup β]

section Preorder

variable [Preorder ι] [LocallyFiniteOrderBot ι]

def partialSups (f : ι → α) : ι →o α where
  toFun i := (Iic i).sup' nonempty_Iic f
  monotone' _ _ hmn := sup'_mono f (Iic_subset_Iic.mpr hmn) nonempty_Iic

lemma partialSups_iff_forall {f : ι → α} (p : α → Prop)
    (hp : ∀ {a b}, p (a ⊔ b) ↔ p a ∧ p b) {i : ι} :
    p (partialSups f i) ↔ ∀ j ≤ i, p (f j) := by
  classical
  rw [partialSups_apply, comp_sup'_eq_sup'_comp (γ := Propᵒᵈ) _ p, sup'_eq_sup]
  · change (Iic i).inf (p ∘ f) ↔ _
    simp [Finset.inf_eq_iInf]
  · intro x y
    rw [hp]
    rfl
