/-
Extracted from RingTheory/Ideal/Prod.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Ideals in product rings

For commutative rings `R` and `S` and ideals `I ≤ R`, `J ≤ S`, we define `Ideal.prod I J` as the
product `I × J`, viewed as an ideal of `R × S`. In `ideal_prod_eq` we show that every ideal of
`R × S` is of this form.  Furthermore, we show that every prime ideal of `R × S` is of the form
`p × S` or `R × p`, where `p` is a prime ideal.
-/

universe u v

variable {R : Type u} {S : Type v} [Semiring R] [Semiring S] (I : Ideal R) (J : Ideal S)

namespace Ideal

def prod : Ideal (R × S) := I.comap (RingHom.fst R S) ⊓ J.comap (RingHom.snd R S)
