/-
Extracted from LinearAlgebra/QuadraticForm/Basic.lean
Genuine: 9 of 9 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Quadratic maps

This file defines quadratic maps on an `R`-module `M`, taking values in an `R`-module `N`.
An `N`-valued quadratic map on a module `M` over a commutative ring `R` is a map `Q : M → N` such
that:

* `QuadraticMap.map_smul`: `Q (a • x) = (a * a) • Q x`
* `QuadraticMap.polar_add_left`, `QuadraticMap.polar_add_right`,
  `QuadraticMap.polar_smul_left`, `QuadraticMap.polar_smul_right`:
  the map `QuadraticMap.polar Q := fun x y ↦ Q (x + y) - Q x - Q y` is bilinear.

This notion generalizes to commutative semirings using the approach in [izhakian2016][] which
requires that there be a (possibly non-unique) companion bilinear map `B` such that
`∀ x y, Q (x + y) = Q x + Q y + B x y`. Over a ring, this `B` is precisely `QuadraticMap.polar Q`.

To build a `QuadraticMap` from the `polar` axioms, use `QuadraticMap.ofPolar`.

Quadratic maps come with a scalar multiplication, `(a • Q) x = a • Q x`,
and composition with linear maps `f`, `Q.comp f x = Q (f x)`.

## Main definitions

* `QuadraticMap.ofPolar`: a more familiar constructor that works on rings
* `QuadraticMap.associated`: associated bilinear map
* `QuadraticMap.PosDef`: positive definite quadratic maps
* `QuadraticMap.Anisotropic`: anisotropic quadratic maps
* `QuadraticMap.discr`: discriminant of a quadratic map
* `QuadraticMap.IsOrtho`: orthogonality of vectors with respect to a quadratic map.

## Main statements

* `QuadraticMap.associated_left_inverse`,
* `QuadraticMap.associated_rightInverse`: in a commutative ring where 2 has
  an inverse, there is a correspondence between quadratic maps and symmetric
  bilinear forms
* `LinearMap.BilinForm.exists_orthogonal_basis`: There exists an orthogonal basis with
  respect to any nondegenerate, symmetric bilinear map `B`.

## Notation

In this file, the variable `R` is used when a `CommSemiring` structure is available.

The variable `S` is used when `R` itself has a `•` action.

## Implementation notes

While the definition and many results make sense if we drop commutativity assumptions,
the correct definition of a quadratic maps in the noncommutative setting would require
substantial refactors from the current version, such that $Q(rm) = rQ(m)r^*$ for some
suitable conjugation $r^*$.

The [Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Quadratic.20Maps/near/395529867)
has some further discussion.

## References

* https://en.wikipedia.org/wiki/Quadratic_form
* https://en.wikipedia.org/wiki/Discriminant#Quadratic_forms

## Tags

quadratic map, homogeneous polynomial, quadratic polynomial
-/

universe u v w

variable {S T : Type*}

variable {R : Type*} {M N P A : Type*}

open LinearMap (BilinMap BilinForm)

section Polar

variable [CommRing R] [AddCommGroup M] [AddCommGroup N]

namespace QuadraticMap

def polar (f : M → N) (x y : M) :=
  f (x + y) - f x - f y

protected theorem map_add (f : M → N) (x y : M) :
    f (x + y) = f x + f y + polar f x y := by
  rw [polar]
  abel

theorem polar_add (f g : M → N) (x y : M) : polar (f + g) x y = polar f x y + polar g x y := by
  simp only [polar, Pi.add_apply]
  abel

theorem polar_neg (f : M → N) (x y : M) : polar (-f) x y = -polar f x y := by
  simp only [polar, Pi.neg_apply, sub_eq_add_neg, neg_add]

theorem polar_smul [Monoid S] [DistribMulAction S N] (f : M → N) (s : S) (x y : M) :
    polar (s • f) x y = s • polar f x y := by simp only [polar, Pi.smul_apply, smul_sub]

theorem polar_comm (f : M → N) (x y : M) : polar f x y = polar f y x := by
  rw [polar, polar, add_comm, sub_sub, sub_sub, add_comm (f x) (f y)]

theorem polar_add_left_iff {f : M → N} {x x' y : M} :
    polar f (x + x') y = polar f x y + polar f x' y ↔
      f (x + x' + y) + (f x + f x' + f y) = f (x + x') + f (x' + y) + f (y + x) := by
  simp only [← add_assoc]
  simp only [polar, sub_eq_iff_eq_add, eq_sub_iff_add_eq, sub_add_eq_add_sub, add_sub]
  simp only [add_right_comm _ (f y) _, add_right_comm _ (f x') (f x)]
  rw [add_comm y x, add_right_comm _ _ (f (x + y)), add_comm _ (f (x + y)),
    add_right_comm (f (x + y)), add_left_inj]

theorem polar_comp {F : Type*} [AddCommGroup S] [FunLike F N S] [AddMonoidHomClass F N S]
    (f : M → N) (g : F) (x y : M) :
    polar (g ∘ f) x y = g (polar f x y) := by
  simp only [polar, Function.comp_apply, map_sub]

def polarSym2 (f : M → N) : Sym2 M → N :=
  Sym2.lift ⟨polar f, polar_comm _⟩
