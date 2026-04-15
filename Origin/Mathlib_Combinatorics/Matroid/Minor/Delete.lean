/-
Extracted from Combinatorics/Matroid/Minor/Delete.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Matroid Deletion

For `M : Matroid α` and `X : Set α`, the *deletion* of `X` from `M` is the matroid `M ＼ X`
with ground set `M.E \ X`, in which a subset of `M.E \ X` is independent if and only if it is
independent in `M`.

The deletion `M ＼ X` is equal to the restriction `M ↾ (M.E \ X)`, but is of special importance
in the theory because it is the dual notion of *contraction*, and thus plays a more central
and natural role than restriction in many contexts.

Because of the implementation of the restriction `M ↾ R` allowing `R` to not be a subset of `M.E`,
the relation `M ↾ R ≤r M` holds only with the assumption `R ⊆ M.E`,
whereas `M ＼ D`, being defined as `M ↾ (M.E \ D)`, satisfies `M ＼ D ≤r M` unconditionally.
This is often quite convenient.

## Main Declarations

* `Matroid.delete M D`, written `M ＼ D`, is the restriction of `M` to the set `M.E \ D`,
  or equivalently the matroid on `M.E \ D` whose independent sets are the `M`-independent sets.

## Naming conventions

We use the abbreviation `deleteElem` in lemma names to refer to the deletion `M ＼ {e}`
of a single element `e : α` from `M : Matroid α`.
-/

open Set

variable {α : Type*} {M M' N : Matroid α} {e f : α} {I B D R X : Set α}

namespace Matroid

/-! ## Deletion -/

section Delete

def delete (M : Matroid α) (D : Set α) : Matroid α := M ↾ (M.E \ D)

scoped infixl:75 " ＼ " => Matroid.delete
