/-
Extracted from Algebra/Symmetrized.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Symmetrized algebra

A commutative multiplication on a real or complex space can be constructed from any multiplication
by "symmetrization" i.e.
$$
a \circ b = \frac{1}{2}(ab + ba)
$$

We provide the symmetrized version of a type `α` as `SymAlg α`, with notation `αˢʸᵐ`.

## Implementation notes

The approach taken here is inspired by `Mathlib/Algebra/Opposites.lean`. We use Oxford Spellings
(IETF en-GB-oxendict).

## Note

See `SymmetricAlgebra` instead if you are looking for the symmetric algebra of a module.

## References

* [Hanche-Olsen and Størmer, Jordan Operator Algebras][hancheolsenstormer1984]
-/

open Function

def SymAlg (α : Type*) : Type _ :=
  α
