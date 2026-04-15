/-
Extracted from Algebra/Ring/Prod.lean
Genuine: 2 of 15 | Dissolved: 0 | Infrastructure: 13
-/
import Origin.Core

/-!
# Semiring, ring etc. structures on `R × S`

In this file we define two-binop (`Semiring`, `Ring` etc) structures on `R × S`. We also prove
trivial `simp` lemmas, and define the following operations on `RingHom`s and similarly for
`NonUnitalRingHom`s:

* `fst R S : R × S →+* R`, `snd R S : R × S →+* S`: projections `Prod.fst` and `Prod.snd`
  as `RingHom`s;
* `f.prod g : R →+* S × T`: sends `x` to `(f x, g x)`;
* `f.prod_map g : R × S → R' × S'`: `Prod.map f g` as a `RingHom`,
  sends `(x, y)` to `(f x, g y)`.
-/

variable {R R' S S' T : Type*}

namespace Prod

-- INSTANCE (free from Core): instDistrib

-- INSTANCE (free from Core): instNonUnitalNonAssocSemiring

-- INSTANCE (free from Core): instNonUnitalSemiring

-- INSTANCE (free from Core): instNonAssocSemiring

-- INSTANCE (free from Core): instSemiring

-- INSTANCE (free from Core): instNonUnitalCommSemiring

-- INSTANCE (free from Core): instCommSemiring

-- INSTANCE (free from Core): instNonUnitalNonAssocRing

-- INSTANCE (free from Core): instNonUnitalRing

-- INSTANCE (free from Core): instNonAssocRing

-- INSTANCE (free from Core): instRing

-- INSTANCE (free from Core): instNonUnitalCommRing

-- INSTANCE (free from Core): instCommRing

end Prod

namespace NonUnitalRingHom

variable (R S) [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]

def fst : R × S →ₙ+* R :=
  { MulHom.fst R S, AddMonoidHom.fst R S with toFun := Prod.fst }

def snd : R × S →ₙ+* S :=
  { MulHom.snd R S, AddMonoidHom.snd R S with toFun := Prod.snd }

variable {R S}
