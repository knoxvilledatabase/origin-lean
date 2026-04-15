/-
Extracted from Algebra/Algebra/TransferInstance.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Transfer algebraic structures across `Equiv`s

This continues the pattern set in `Mathlib/Algebra/Group/TransferInstance.lean`.
-/

universe v

variable {R α β : Type*} [CommSemiring R]

namespace Equiv

variable (e : α ≃ β)

variable (R) in

protected abbrev algebra (e : α ≃ β) [Semiring β] :
    let _ := Equiv.semiring e
    ∀ [Algebra R β], Algebra R α := fast_instance%
  letI := Equiv.semiring e
  letI := e.smul R
  { algebraMap :=
    { toFun r := e.symm (algebraMap R β r)
      __ := e.ringEquiv.symm.toRingHom.comp (algebraMap R β) }
    commutes' r x :=
      show e.symm ((e (e.symm (algebraMap R β r)) * e x)) =
          e.symm (e x * e (e.symm (algebraMap R β r))) by
        simp [Algebra.commutes]
    smul_def' r x :=
      show e.symm (r • e x) = e.symm (e (e.symm (algebraMap R β r)) * e x) by
        simp [Algebra.smul_def] }

variable (R) in

def algEquiv (e : α ≃ β) [Semiring β] [Algebra R β] : by
    let semiring := Equiv.semiring e
    let algebra := Equiv.algebra R e
    exact α ≃ₐ[R] β := by
  intros
  exact
    { Equiv.ringEquiv e with
      commutes' := fun r => by
        apply e.symm.injective
        simp only [RingEquiv.toEquiv_eq_coe, toFun_as_coe, EquivLike.coe_coe, ringEquiv_apply,
          symm_apply_apply, algebraMap_def] }
