/-
Extracted from Algebra/DualQuaternion.lean
Genuine: 1 | Conflates: 0 | Dissolved: 0 | Infrastructure: 16
-/
import Origin.Core
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.Quaternion

noncomputable section

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

/-! Lemmas characterizing `Quaternion.dualNumberEquiv`. -/

end Quaternion
