/-
Extracted from LinearAlgebra/Transvection/Basic.lean
Genuine: 5 of 6 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Transvections in a module

* When `f : Module.Dual R V` and `v : V`,
  `LinearMap.transvection f v` is the linear map given by `x ↦ x + f x • v`,

* `LinearMap.transvection.det` shows that the determinant of
  `LinearMap.transvection f v` is equal to `1 + f v`.

* If, moreover, `f v = 0`, then `LinearEquiv.transvection` shows that it is
  a linear equivalence.

* `LinearMap.transvections R V`: the set of transvections.

* `LinearEquiv.dilatransvections R V`: the set of linear equivalences
  whose associated linear map is of the form `LinearMap.transvection f v`.

* `LinearEquiv.transvection.det` shows that it has determinant `1`.

## Note on terminology

In the mathematical literature, linear maps of the form `LinearMap.transvection f v`
are only called “transvections” when `f v = 0`. Otherwise, they are sometimes
called “dilations” (especially if `f v ≠ -1`).

The definition is almost the same as that of `Module.preReflection f v`,
up to a sign change, which are interesting when `f v = 2`, because they give “reflections”.

-/

namespace LinearMap

open Module

variable {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]

def transvection (f : Dual R V) (v : V) : V →ₗ[R] V where
  toFun x := x + f x • v
  map_add' x y := by simp [add_add_add_comm, add_smul]
  map_smul' r x := by simp [smul_eq_mul, smul_add, mul_smul]

namespace transvection

open Submodule LinearMap

theorem comp_of_left_eq_apply {f : Dual R V} {v w : V} {x : V} (hw : f w = 0) :
    transvection f v (transvection f w x) = transvection f (v + w) x := by
  simp [transvection, map_add, hw, add_assoc]

theorem comp_of_left_eq {f : Dual R V} {v w : V} (hw : f w = 0) :
    (transvection f v) ∘ₗ (transvection f w) = transvection f (v + w) := by
  ext; simp [comp_of_left_eq_apply hw]

theorem comp_of_right_eq_apply {f g : Dual R V} {v : V} {x : V} (hf : f v = 0) :
    (transvection f v) (transvection g v x) = transvection (f + g) v x := by
  simp [transvection, map_add, hf, add_smul, add_assoc]

theorem comp_of_right_eq {f g : Dual R V} {v : V} (hf : f v = 0) :
    (transvection f v) ∘ₗ (transvection g v) = transvection (f + g) v := by
  ext; simp [comp_of_right_eq_apply hf]
