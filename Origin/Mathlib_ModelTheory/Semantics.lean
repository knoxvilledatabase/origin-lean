/-
Extracted from ModelTheory/Semantics.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Basics on First-Order Semantics

This file defines the interpretations of first-order terms, formulas, sentences, and theories
in a style inspired by the [Flypitch project](https://flypitch.github.io/).

## Main Definitions

- `FirstOrder.Language.Term.realize` is defined so that `t.realize v` is the term `t` evaluated at
  variables `v`.
- `FirstOrder.Language.BoundedFormula.Realize` is defined so that `φ.Realize v xs` is the bounded
  formula `φ` evaluated at tuples of variables `v` and `xs`.
- `FirstOrder.Language.Formula.Realize` is defined so that `φ.Realize v` is the formula `φ`
  evaluated at variables `v`.
- `FirstOrder.Language.Sentence.Realize` is defined so that `φ.Realize M` is the sentence `φ`
  evaluated in the structure `M`. Also denoted `M ⊨ φ`.
- `FirstOrder.Language.Theory.Model` is defined so that `T.Model M` is true if and only if every
  sentence of `T` is realized in `M`. Also denoted `T ⊨ φ`.

## Main Results

- Several results in this file show that syntactic constructions such as `relabel`, `castLE`,
  `liftAt`, `subst`, and the actions of language maps commute with realization of terms, formulas,
  sentences, and theories.

## Implementation Notes

- `BoundedFormula` uses a locally nameless representation with bound variables as well-scoped de
  Bruijn levels. See the implementation note in `Syntax.lean` for details.

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

variable {L : Language.{u, v}} {L' : Language}

variable {M : Type w} {N P : Type*} [L.Structure M] [L.Structure N] [L.Structure P]

variable {α : Type u'} {β : Type v'} {γ : Type*}

open FirstOrder Cardinal

open Structure Fin

namespace Term

def realize (v : α → M) : ∀ _t : L.Term α, M
  | var k => v k
  | func f ts => funMap f fun i => (ts i).realize v
