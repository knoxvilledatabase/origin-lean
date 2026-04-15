/-
Extracted from Data/Finsupp/Fin.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# `cons` and `tail` for maps `Fin n →₀ M`

We interpret maps `Fin n →₀ M` as `n`-tuples of elements of `M`,
We define the following operations:
* `Finsupp.tail` : the tail of a map `Fin (n + 1) →₀ M`, i.e., its last `n` entries;
* `Finsupp.cons` : adding an element at the beginning of an `n`-tuple, to get an `n + 1`-tuple;

In this context, we prove some usual properties of `tail` and `cons`, analogous to those of
`Data.Fin.Tuple.Basic`.
-/

open Function

noncomputable section

namespace Finsupp

variable {n : ℕ} (i : Fin n) {M : Type*} [Zero M] (y : M) (t : Fin (n + 1) →₀ M) (s : Fin n →₀ M)

def tail (s : Fin (n + 1) →₀ M) : Fin n →₀ M :=
  Finsupp.equivFunOnFinite.symm (Fin.tail s)

def cons (y : M) (s : Fin n →₀ M) : Fin (n + 1) →₀ M :=
  Finsupp.equivFunOnFinite.symm (Fin.cons y s : Fin (n + 1) → M)
