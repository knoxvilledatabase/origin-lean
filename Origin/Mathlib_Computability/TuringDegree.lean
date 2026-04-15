/-
Extracted from Computability/TuringDegree.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Turing degrees

This file defines Turing reducibility and equivalence, proves that Turing equivalence is an
equivalence relation, and defines Turing degrees as the quotient under this relation.

## Main definitions

- `TuringReducible`: A relation defining Turing reducibility between partial functions.
- `TuringEquivalent`: An equivalence relation defining Turing equivalence between partial functions.
- `TuringDegree`: The type of Turing degrees, defined as the quotient of partial functions under
  `TuringEquivalent`.

## Notation

- `f ≤ᵀ g` : `f` is Turing reducible to `g`.
- `f ≡ᵀ g` : `f` is Turing equivalent to `g`.

## References

* [Odifreddi1989] Odifreddi, Piergiorgio.
  *Classical Recursion Theory: The Theory of Functions and Sets of Natural Numbers,
  Vol. I*. Springer-Verlag, 1989.

## Tags

Computability, Oracle, Turing Degrees, Reducibility, Equivalence Relation
-/

open Primrec

variable {f g h : ℕ →. ℕ}

abbrev TuringReducible (f g : ℕ →. ℕ) : Prop :=
  RecursiveIn {g} f

abbrev TuringEquivalent (f g : ℕ →. ℕ) : Prop :=
  AntisymmRel TuringReducible f g
