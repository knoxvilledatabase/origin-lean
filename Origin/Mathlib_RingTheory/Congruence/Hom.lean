/-
Extracted from RingTheory/Congruence/Hom.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Congruence relations and ring homomorphisms

This file contains elementary definitions involving congruence
relations and morphisms for rings and semirings

## Main definitions

* `RingCon.ker`: the kernel of a monoid homomorphism as a congruence relation
* `RingCon.lift`, `RingCon.liftₐ`: the homomorphism / the algebra morphism
  on the quotient given that the congruence is in the kernel
* `RingCon.map`, `RingCon.mapₐ`: homomorphism / algebra morphism
  from a smaller to a larger quotient

* `RingCon.quotientKerEquivRangeS`, `RingCon.quotientKerEquivRange`,
  `RingCon.quotientKerEquivRangeₐ` :
  the first isomorphism theorem for semirings (using `RingHom.rangeS`),
  rings (using `RingHom.range`) and algebras (using `AlgHom.range`).
* `RingCon.comapQuotientEquivRangeS`, `RingCon.comapQuotientEquivRange`,
  `RingCon.comapQuotientEquivRangeₐ` : the second isomorphism theorem
  for semirings (using `RingHom.rangeS`), rings (using `RingHom.range`)
  and algebras (using `AlgHom.range`).

* `RingCon.quotientQuotientEquivQuotient`, `RingCon.quotientQuotientEquivQuotientₐ` :
  the third isomorphism theorem for semirings (or rings) and algebras

## Tags

congruence, congruence relation, quotient, quotient by congruence relation, ring,
quotient ring
-/

variable {M : Type*} {N : Type*} {P : Type*}

open Function Setoid

namespace RingCon

variable [NonAssocSemiring M] [NonAssocSemiring N] [NonAssocSemiring P] {c d : RingCon M}

def ker (f : M →+* N) : RingCon M := comap ⊥ f
