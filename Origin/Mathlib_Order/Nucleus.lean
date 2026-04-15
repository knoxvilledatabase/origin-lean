/-
Extracted from Order/Nucleus.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Nucleus

Locales are the dual concept to frames. Locale theory is a branch of point-free topology, where
intuitively locales are like topological spaces which may or may not have enough points.
Sublocales of a locale generalize the concept of subspaces in topology to the point-free setting.

A nucleus is an endomorphism of a frame which corresponds to a sublocale.

## References
https://ncatlab.org/nlab/show/sublocale
https://ncatlab.org/nlab/show/nucleus
-/

open Order InfHom Set

variable {X : Type*}

structure Nucleus (X : Type*) [SemilatticeInf X] extends InfHom X X where
  /-- A nucleus is idempotent.

  Do not use this directly. Instead use `NucleusClass.idempotent`. -/
  idempotent' (x : X) : toFun (toFun x) ≤ toFun x
  /-- A nucleus is increasing.

  Do not use this directly. Instead use `NucleusClass.le_apply`. -/
  le_apply' (x : X) : x ≤ toFun x

class NucleusClass (F X : Type*) [SemilatticeInf X] [FunLike F X X] : Prop
    extends InfHomClass F X X where
  /-- A nucleus is idempotent. -/
  idempotent (x : X) (f : F) : f (f x) ≤ f x
  /-- A nucleus is inflationary. -/
  le_apply (x : X) (f : F) : x ≤ f x

namespace Nucleus

section SemilatticeInf

variable [SemilatticeInf X] {n m : Nucleus X} {x y : X}

-- INSTANCE (free from Core): :

def Simps.apply (n : Nucleus X) : X → X := n
