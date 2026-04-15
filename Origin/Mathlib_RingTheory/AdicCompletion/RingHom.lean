/-
Extracted from RingTheory/AdicCompletion/RingHom.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lift of ring homomorphisms to adic completions
Let `R`, `S` be rings, `I` be an ideal of `S`.
In this file we prove that a compatible family of ring homomorphisms from a ring `R` to
`S ⧸ I ^ n` can be lifted to a ring homomorphism `R →+* AdicCompletion I S`.
If `S` is `I`-adically complete, then this compatible family of ring homomorphisms can be
lifted to a ring homomorphism `R →+* S`.

## Main definitions

- `IsAdicComplete.liftRingHom`: if `R` is
  `I`-adically complete, then a compatible family of
  ring maps `S →+* R ⧸ I ^ n` can be lifted to a unique ring map `S →+* R`.
  Together with `mk_liftRingHom_apply` and `eq_liftRingHom`, it gives the universal property
  of `R` being `I`-adically complete.
-/

open Ideal Quotient

variable {R S : Type*} [NonAssocSemiring R] [CommRing S] (I : Ideal S)

namespace IsAdicComplete

open AdicCompletion

variable [IsAdicComplete I S] (f : (n : ℕ) → R →+* S ⧸ I ^ n)
    (hf : ∀ {m n : ℕ} (hle : m ≤ n), (factorPow I hle).comp (f n) = f m)

noncomputable def liftRingHom :
    R →+* S :=
  ((ofAlgEquiv I).symm : _ →+* _).comp (AdicCompletion.liftRingHom I f hf)
