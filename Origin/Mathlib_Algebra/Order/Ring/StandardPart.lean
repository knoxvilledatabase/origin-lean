/-
Extracted from Algebra/Order/Ring/StandardPart.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Standard part function

Given a finite element in a non-archimedean field, the standard part function rounds it to the
unique closest real number. That is, it chops off any infinitesimals.

Let `K` be a linearly ordered field. The subset of finite elements (i.e. those bounded by a natural
number) is a `ValuationSubring`, which means we can construct its residue field
`FiniteResidueField`, roughly corresponding to the finite elements quotiented by infinitesimals.
This field inherits a `LinearOrder` instance, which makes it into an Archimedean linearly ordered
field, meaning we can uniquely embed it in the reals.

Given a finite element of the field, the `ArchimedeanClass.stdPart` function returns the real number
corresponding to this unique embedding. This function generalizes, among other things, the standard
part function on `Hyperreal`.

## References

* https://en.wikipedia.org/wiki/Standard_part_function
-/

namespace ArchimedeanClass

variable
  {K : Type*} [LinearOrder K] [Field K] [IsOrderedRing K] {x y : K}
  {R : Type*} [LinearOrder R] [CommRing R] [IsStrictOrderedRing R] [Archimedean R]

/-! ### Finite residue field -/

variable (K) in

def FiniteElement : Type _ :=
  (addValuation K).toValuation.valuationSubring

deriving CommRing, IsDomain, ValuationRing, LinearOrder, IsStrictOrderedRing

namespace FiniteElement
