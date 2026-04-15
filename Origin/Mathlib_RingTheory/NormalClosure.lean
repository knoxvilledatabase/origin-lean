/-
Extracted from RingTheory/NormalClosure.lean
Genuine: 1 of 27 | Dissolved: 0 | Infrastructure: 26
-/
import Origin.Core

/-!
# Normal closure of an extension of domains

We define the normal closure of an extension of domains `R ⊆ S` as a domain `T` such that
`R ⊆ S ⊆ T` and the extension `Frac T / Frac R` is Galois, and prove several instances about it.

Under the hood, `T` is defined as the `integralClosure` of `S` inside the
`IntermediateField.normalClosure` of the extension `Frac S / Frac R` inside the `AlgebraicClosure`
of `Frac S`. In particular, if `S` is a Dedekind domain, then `T` is also a Dedekind domain.

## Technical notes

* Many instances are proved about the `IntermediateField.normalClosure` of the extension
  `Frac S / Frac R` inside the `AlgebraicClosure` of `Frac S`. However these are only needed for the
  construction of `T` and to prove some results about it. Therefore, these instances are local.
* `Ring.NormalClosure` is defined as a type rather than a `Subalgebra` for performance reasons
  (and thus we need to provide explicit instances for it). Although defining it as a `Subalgebra`
  does not cause timeouts in this file, it does slow down considerably its compilation and
  does trigger timeouts in applications.
-/

namespace Ring

noncomputable section NormalClosure

variable (R S : Type*) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [Algebra R S] [Module.IsTorsionFree R S]

-- INSTANCE (free from Core): :

local notation3 "K" => FractionRing R

local notation3 "L" => FractionRing S

local notation3 "E" => IntermediateField.normalClosure (FractionRing R) (FractionRing S)

    (AlgebraicClosure (FractionRing S))

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

def NormalClosure : Type _ := integralClosure S E

local notation3 "T" => NormalClosure R S

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

variable [Module.Finite R S]

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

variable [PerfectField (FractionRing R)]

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

variable [IsDedekindDomain S]

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

end Ring.NormalClosure
