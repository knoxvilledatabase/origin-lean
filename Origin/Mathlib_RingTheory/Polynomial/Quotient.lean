/-
Extracted from RingTheory/Polynomial/Quotient.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Quotients of polynomial rings
-/

open Polynomial

namespace Polynomial

variable {R : Type*} [CommRing R]

noncomputable def quotientSpanXSubCAlgEquiv (x : R) :
    (R[X] ⧸ Ideal.span ({X - C x} : Set R[X])) ≃ₐ[R] R :=
  let e := RingHom.quotientKerEquivOfRightInverse (fun x => by
    exact eval_C : Function.RightInverse (fun a : R => (C a : R[X])) (@aeval R R _ _ _ x))
  (Ideal.quotientEquivAlgOfEq R (ker_evalRingHom x).symm).trans
    { e with commutes' := fun r => e.apply_symm_apply r }
