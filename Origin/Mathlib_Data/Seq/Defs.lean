/-
Extracted from Data/Seq/Defs.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Possibly infinite lists

This file provides `Stream'.Seq α`, a type representing possibly infinite lists (referred here as
sequences). It is encoded as an infinite stream of options such that if `f n = none`, then
`f m = none` for all `m ≥ n`.

## Main definitions

* `Seq α`: The type of possibly infinite lists (sequences) encoded as streams of options. It is
  encoded as `Stream' (Option α)` such that if `f n = none`, then `f m = none` for all `m ≥ n`.
  It has two "constructors": `nil` and `cons`, and a destructor `destruct`.
* `Seq1 α`: The type of nonempty sequences
* `Seq.get?`: Extract the nth element of a sequence (if it exists).
* `Seq.corec`: Corecursion principle for `Seq α` as a coinductive type.
* `Seq.Terminates`: Predicate for when a sequence is finite.

One can convert between sequences and other types: `List`, `Stream'`, `MLList` using corresponding
functions defined in this file.

There are also a number of operations and predicates on sequences mirroring those on lists:
`Seq.map`, `Seq.zip`, `Seq.zipWith`, `Seq.unzip`, `Seq.fold`, `Seq.update`, `Seq.drop`,
`Seq.splitAt`, `Seq.append`, `Seq.join`, `Seq.enum`, `Seq.Pairwise`,
as well as a cases principle `Seq.recOn` which allows one to reason about
sequences by cases (`nil` and `cons`).

## Main statements

* `eq_of_bisim`: Bisimulation principle for sequences.
-/

namespace Stream'

universe u v w

def IsSeq {α : Type u} (s : Stream' (Option α)) : Prop :=
  ∀ {n : ℕ}, s n = none → s (n + 1) = none

def Seq (α : Type u) : Type u :=
  { f : Stream' (Option α) // f.IsSeq }

def Seq1 (α) :=
  α × Seq α

namespace Seq

variable {α : Type u} {β : Type v} {γ : Type w}

def get? : Seq α → ℕ → Option α :=
  Subtype.val
