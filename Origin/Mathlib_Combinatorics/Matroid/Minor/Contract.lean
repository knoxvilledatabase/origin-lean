/-
Extracted from Combinatorics/Matroid/Minor/Contract.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Matroid Contraction

Instead of deleting the elements of `X : Set α` from `M : Matroid α`, we can contract them.
The *contraction* of `X` from `M`, denoted `M ／ X`, is the matroid on ground set `M.E \ X`
in which a set `I` is independent if and only if `I ∪ J` is independent in `M`,
where `J` is an arbitrarily chosen basis for `X`. Contraction corresponds to contracting
edges in graphic matroids (hence the name) and corresponds to projecting to a quotient
space in the case of linearly representable matroids. It is an important notion in both
these settings.

We can also define contraction much more tersely in terms of deletion and duality
with `M ／ X = (M✶ ＼ X)✶`: that is, contraction is the dual operation of deletion.
While this is perhaps less intuitive, we use this very concise expression as the definition,
and prove with the lemma `Matroid.IsBasis.contract_indep_iff` that this is equivalent to
the more verbose definition above.

## Main Declarations

* `Matroid.contract M C`, written `M ／ C`, is the matroid on ground set `M.E \ C` in which a set
  `I ⊆ M.E \ C` is independent if and only if `I ∪ J` is independent in `M`,
  where `J` is an arbitrary basis for `C`.
* `Matroid.contract_dual M C : (M ／ X)✶ = M✶ ＼ X`; the dual of contraction is deletion.
* `Matroid.delete_dual M C : (M ＼ X)✶ = M✶ ／ X`; the dual of deletion is contraction.
* `Matroid.IsBasis.contract_indep_iff`; if `I` is a basis for `C`, then the independent
  sets of `M ／ C` are exactly the `J ⊆ M.E \ C` for which `I ∪ J` is independent in `M`.
* `Matroid.contract_delete_comm` : `M ／ C ＼ D = M ＼ D ／ C` for disjoint `C` and `D`.

## Naming conventions

Mirroring the convention for deletion, we use the abbreviation `contractElem` in lemma names
to refer to the contraction `M ／ {e}` of a single element `e : α` from `M : Matroid α`.
-/

open Set

variable {α : Type*} {M M' N : Matroid α} {e f : α} {I J R D B X Y Z K : Set α}

namespace Matroid

section Contract

variable {C C₁ C₂ : Set α}

def contract (M : Matroid α) (C : Set α) : Matroid α := (M✶ ＼ C)✶

scoped infixl:75 " ／ " => Matroid.contract
