/-
Extracted from ModelTheory/LanguageMap.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Language Maps

Maps between first-order languages in the style of the
[Flypitch project](https://flypitch.github.io/), as well as several important maps between
structures.

## Main Definitions

- A `FirstOrder.Language.LHom`, denoted `L →ᴸ L'`, is a map between languages, sending the symbols
  of one to symbols of the same kind and arity in the other.
- A `FirstOrder.Language.LEquiv`, denoted `L ≃ᴸ L'`, is an invertible language homomorphism.
- `FirstOrder.Language.withConstants` is defined so that if `M` is an `L.Structure` and
  `A : Set M`, `L.withConstants A`, denoted `L[[A]]`, is a language which adds constant symbols for
  elements of `A` to `L`.

## References

For the Flypitch project:
- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum hypothesis*]
  [flypitch_cpp]
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
  the continuum hypothesis*][flypitch_itp]

-/

universe u v u' v' w w'

namespace FirstOrder

namespace Language

open Structure Cardinal

variable (L : Language.{u, v}) (L' : Language.{u', v'}) {M : Type w} [L.Structure M]

structure LHom where
  /-- The mapping of functions -/
  onFunction : ∀ ⦃n⦄, L.Functions n → L'.Functions n := by
    exact fun {n} => isEmptyElim
  /-- The mapping of relations -/
  onRelation : ∀ ⦃n⦄, L.Relations n → L'.Relations n := by
    exact fun {n} => isEmptyElim
