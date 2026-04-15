/-
Extracted from Algebra/DualQuaternion.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Dual quaternions

Similar to the way that rotations in 3D space can be represented by quaternions of unit length,
rigid motions in 3D space can be represented by dual quaternions of unit length.

## Main results

* `Quaternion.dualNumberEquiv`: quaternions over dual numbers or dual
  numbers over quaternions are equivalent constructions.

## References

* <https://en.wikipedia.org/wiki/Dual_quaternion>
-/

variable {R : Type*} [CommRing R]

namespace Quaternion

def dualNumberEquiv : Quaternion (DualNumber R) ≃ₐ[R] DualNumber (Quaternion R) where
  toFun q :=
    (⟨q.re.fst, q.imI.fst, q.imJ.fst, q.imK.fst⟩, ⟨q.re.snd, q.imI.snd, q.imJ.snd, q.imK.snd⟩)
  invFun d :=
    ⟨(d.fst.re, d.snd.re), (d.fst.imI, d.snd.imI), (d.fst.imJ, d.snd.imJ), (d.fst.imK, d.snd.imK)⟩
  map_mul' := by
    intros
    ext : 1
    · rfl
    · dsimp
      congr 1 <;> simp <;> ring
  map_add' := by
    intros
    rfl
  commutes' _ := rfl

/-! Lemmas characterizing `Quaternion.dualNumberEquiv`. -/
