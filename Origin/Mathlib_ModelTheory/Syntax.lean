/-
Extracted from ModelTheory/Syntax.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Basics on First-Order Syntax

This file defines first-order terms, formulas, sentences, and theories in a style inspired by the
[Flypitch project](https://flypitch.github.io/).

## Main Definitions

- A `FirstOrder.Language.Term` is defined so that `L.Term α` is the type of `L`-terms with free
  variables indexed by `α`.
- A `FirstOrder.Language.Formula` is defined so that `L.Formula α` is the type of `L`-formulas with
  free variables indexed by `α`.
- A `FirstOrder.Language.Sentence` is a formula with no free variables.
- A `FirstOrder.Language.Theory` is a set of sentences.
- The variables of terms and formulas can be relabelled with `FirstOrder.Language.Term.relabel`,
  `FirstOrder.Language.BoundedFormula.relabel`, and `FirstOrder.Language.Formula.relabel`.
- Given an operation on terms and an operation on relations,
  `FirstOrder.Language.BoundedFormula.mapTermRel` gives an operation on formulas.
- `FirstOrder.Language.BoundedFormula.castLE` adds more bound variables.
- `FirstOrder.Language.BoundedFormula.liftAt` raises the indexes of the bound variables above a
  particular index.
- `FirstOrder.Language.Term.subst` and `FirstOrder.Language.BoundedFormula.subst` substitute
  variables with given terms.
- `FirstOrder.Language.Term.substFunc` instead substitutes function definitions with given terms.
- Language maps can act on syntactic objects with functions such as
  `FirstOrder.Language.LHom.onFormula`.
- `FirstOrder.Language.Term.constantsVarsEquiv` and
  `FirstOrder.Language.BoundedFormula.constantsVarsEquiv` switch terms and formulas between having
  constants in the language and having extra free variables indexed by the same type.

## Implementation Notes

- `BoundedFormula` uses a locally nameless representation with bound variables as well-scoped de
  Bruijn levels (the variable bounded by the outermost quantifier is indexed by `0`). Specifically,
  a `L.BoundedFormula α n` is a formula with free variables indexed by a type `α`, which cannot be
  quantified over, and bound variables indexed by `Fin n`, which can. For any
  `φ : L.BoundedFormula α (n + 1)`, we define the formula `∀' φ : L.BoundedFormula α n` by
  universally quantifying over the variable indexed by `n : Fin (n + 1)`.

## References

For the Flypitch project:
- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum hypothesis*]
  [flypitch_cpp]
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
  the continuum hypothesis*][flypitch_itp]
-/

universe u v w u' v'

namespace FirstOrder

namespace Language

variable (L : Language.{u, v}) {L' : Language}

variable {M : Type w} {α : Type u'} {β : Type v'} {γ : Type*}

open FirstOrder

open Structure Fin

inductive Term (α : Type u') : Type max u u'
  | var : α → Term α
  | func : ∀ {l : ℕ} (_f : L.Functions l) (_ts : Fin l → Term α), Term α

export Term (var func)

variable {L}

namespace Term

-- INSTANCE (free from Core): instDecidableEq

open Finset
