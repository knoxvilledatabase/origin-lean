/-
Extracted from LinearAlgebra/TensorPower/Symmetric.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Symmetric tensor power of a semimodule over a commutative semiring

We define the `ι`-indexed symmetric tensor power of `M` as the `PiTensorProduct` quotiented by
the relation that the `tprod` of `ι` elements is equal to the `tprod` of the same elements permuted
by a permutation of `ι`. We denote this space by `Sym[R] ι M`, and the canonical multilinear map
from `ι → M` to `Sym[R] ι M` by `⨂ₛ[R] i, f i`. We also reserve the notation `Sym[R]^n M` for the
`n`th symmetric tensor power of `M`, which is the symmetric tensor power indexed by `Fin n`.

## Main definitions:

* `SymmetricPower.module`: the symmetric tensor power is a module over `R`.

## TODO:

* Grading: show that there is a map `Sym[R]^i M × Sym[R]^j M → Sym[R]^(i + j) M` that is
  associative and commutative, and that `n ↦ Sym[R]^n M` is a graded (semi)ring and algebra.
* Universal property: linear maps from `Sym[R]^n M` to `N` correspond to symmetric multilinear
  maps `M ^ n` to `N`.
* Relate to homogeneous (multivariate) polynomials of degree `n`.

-/

suppress_compilation

universe u v

open TensorProduct Equiv

variable (R ι : Type u) [CommSemiring R] (M : Type v) [AddCommMonoid M] [Module R M] (s : ι → M)

inductive SymmetricPower.Rel : (⨂[R] _, M) → (⨂[R] _, M) → Prop
  | perm : (e : Perm ι) → (f : ι → M) → Rel (⨂ₜ[R] i, f i) (⨂ₜ[R] i, f (e i))

def SymmetricPower : Type max u v :=
  (addConGen (SymmetricPower.Rel R ι M)).Quotient

deriving AddCommMonoid
