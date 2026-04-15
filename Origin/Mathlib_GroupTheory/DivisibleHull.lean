/-
Extracted from GroupTheory/DivisibleHull.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Divisible Hull of an abelian group

This file constructs the divisible hull of an `AddCommMonoid` as a `ℕ`-module localized at
`ℕ+` (implemented using `nonZeroDivisors ℕ`), which is a `ℚ≥0`-module.

Furthermore, we show that

* when `M` is a group, so is `DivisibleHull M`, which is also a `ℚ`-module
* when `M` is linearly ordered and cancellative, so is `DivisibleHull M`, which is also an
  ordered `ℚ≥0`-module.
* when `M` is a linearly ordered group, `DivisibleHull M` is an ordered `ℚ`-module, and
  `ArchimedeanClass` is preserved.

Despite the name, this file doesn't implement a `DivisibleBy` instance on `DivisibleHull`. This
should be implemented on `LocalizedModule` in a more general setting (TODO: implement this).
This file mainly focuses on the specialization to `ℕ` and the linear order property introduced by
it.

## Main declarations

* `DivisibleHull M` is the divisible hull of an abelian group.
* `DivisibleHull.archimedeanClassOrderIso M` is the equivalence between `ArchimedeanClass M` and
  `ArchimedeanClass (DivisibleHull M)`.

-/

variable {M : Type*} [AddCommMonoid M]

local notation "↑ⁿ" => PNat.equivNonZeroDivisorsNat

variable (M) in

abbrev DivisibleHull := LocalizedModule (nonZeroDivisors ℕ) M

namespace DivisibleHull

def mk (m : M) (s : ℕ+) : DivisibleHull M := LocalizedModule.mk m (↑ⁿ s)

-- INSTANCE (free from Core): :
