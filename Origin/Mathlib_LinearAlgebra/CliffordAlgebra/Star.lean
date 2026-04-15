/-
Extracted from LinearAlgebra/CliffordAlgebra/Star.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Star structure on `CliffordAlgebra`

This file defines the "clifford conjugation", equal to `reverse (involute x)`, and assigns it the
`star` notation.

This choice is somewhat non-canonical; a star structure is also possible under `reverse` alone.
However, defining it gives us access to constructions like `unitary`.

Most results about `star` can be obtained by unfolding it via `CliffordAlgebra.star_def`.

## Main definitions

* `CliffordAlgebra.instStarRing`

-/

variable {R : Type*} [CommRing R]

variable {M : Type*} [AddCommGroup M] [Module R M]

variable {Q : QuadraticForm R M}

namespace CliffordAlgebra

-- INSTANCE (free from Core): instStarRing

theorem star_def' (x : CliffordAlgebra Q) : star x = involute (reverse x) :=
  reverse_involute _
