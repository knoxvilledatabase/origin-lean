/-
Extracted from RingTheory/Etale/Locus.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Etale locus of an algebra

## Main results
Let `A` be a `R`-algebra.
- `Algebra.etaleLocus` : The set of primes of `A` where it is étale over `R`.
- `Algebra.basicOpen_subset_etaleLocus_iff` :
  `D(f)` is contained in the etale locus if and only if `A_f` is formally etale over `R`.
- `Algebra.etaleLocus_eq_univ_iff` :
  The etale locus is the whole spectrum if and only if `A` is formally etale over `R`.
- `Algebra.isOpen_etaleLocus` :
  If `A` is of finite type over `R`, then the etale locus is open.
-/

namespace Algebra

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra A B]
    [Algebra R B] [IsScalarTower R A B]

variable (R) in

abbrev IsEtaleAt (q : Ideal A) [q.IsPrime] : Prop :=
  FormallyEtale R (Localization.AtPrime q)

variable (R A) in

def etaleLocus : Set (PrimeSpectrum A) :=
  { p | IsEtaleAt R p.asIdeal }
