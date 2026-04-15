/-
Extracted from LinearAlgebra/CliffordAlgebra/Even.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The universal property of the even subalgebra

## Main definitions

* `CliffordAlgebra.even Q`: The even subalgebra of `CliffordAlgebra Q`.
* `CliffordAlgebra.EvenHom`: The type of bilinear maps that satisfy the universal property of the
  even subalgebra
* `CliffordAlgebra.even.lift`: The universal property of the even subalgebra, which states
  that every bilinear map `f` with `f v v = Q v` and `f u v * f v w = Q v • f u w` is in unique
  correspondence with an algebra morphism from `CliffordAlgebra.even Q`.

## Implementation notes

The approach here is outlined in "Computing with the universal properties of the Clifford algebra
and the even subalgebra" (to appear).

The broad summary is that we have two tricks available to us for implementing complex recursors on
top of `CliffordAlgebra.lift`: the first is to use morphisms as the output type, such as
`A = Module.End R N` which is how we obtained `CliffordAlgebra.foldr`; and the second is to use
`N = (N', S)` where `N'` is the value we wish to compute, and `S` is some auxiliary state passed
between one recursor invocation and the next.
For the universal property of the even subalgebra, we apply a variant of the first trick again by
choosing `S` to itself be a submodule of morphisms.
-/

namespace CliffordAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

variable {Q : QuadraticForm R M}

variable {A B : Type*} [Ring A] [Ring B] [Algebra R A] [Algebra R B]

open scoped DirectSum

variable (Q)

def even : Subalgebra R (CliffordAlgebra Q) :=
  (evenOdd Q 0).toSubalgebra (SetLike.one_mem_graded _) fun _x _y hx hy =>
    add_zero (0 : ZMod 2) ▸ SetLike.mul_mem_graded hx hy
