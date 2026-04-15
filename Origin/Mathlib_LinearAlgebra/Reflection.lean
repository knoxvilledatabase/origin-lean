/-
Extracted from LinearAlgebra/Reflection.lean
Genuine: 7 of 7 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Reflections in linear algebra

Given an element `x` in a module `M` together with a linear form `f` on `M` such that `f x = 2`, the
map `y ↦ y - (f y) • x` is an involutive endomorphism of `M`, such that:
 1. the kernel of `f` is fixed,
 2. the point `x` maps to `-x`.

Such endomorphisms are often called reflections of the module `M`. When `M` carries an inner product
for which `x` is perpendicular to the kernel of `f`, then (with mild assumptions) the endomorphism
is characterised by properties 1 and 2 above, and is a linear isometry.

## Main definitions / results:

* `Module.preReflection`: the definition of the map `y ↦ y - (f y) • x`. Its main utility lies in
  the fact that it does not require the assumption `f x = 2`, giving the user freedom to defer
  discharging this proof obligation.
* `Module.reflection`: the definition of the map `y ↦ y - (f y) • x`. This requires the assumption
  that `f x = 2` but by way of compensation it produces a linear equivalence rather than a mere
  linear map.
* `Module.reflection_mul_reflection_pow_apply`: a formula for $(r_1 r_2)^m z$, where $r_1$ and
  $r_2$ are reflections and $z \in M$. It involves the Chebyshev polynomials and holds over any
  commutative ring. This is used to define reflection representations of Coxeter groups.
* `Module.Dual.eq_of_preReflection_mapsTo`: a uniqueness result about reflections that preserve
  finite spanning sets. It is useful in the theory of root data / systems.

## TODO

Related definitions of reflection exist elsewhere in the library. These more specialised
definitions, which require an ambient `InnerProductSpace` structure, are `reflection` (of type
`LinearIsometryEquiv`) and `EuclideanGeometry.reflection` (of type `AffineIsometryEquiv`). We
should connect (or unify) these definitions with `Module.reflection` defined here.

-/

open Function Set

open Module

open Submodule (span)

noncomputable section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (x : M) (f : Dual R M) (y : M)

namespace Module

def preReflection : End R M :=
  LinearMap.id - f.smulRight x

lemma preReflection_apply :
    preReflection x f y = y - (f y) • x := by
  simp [preReflection]

variable {x f}

lemma preReflection_apply_self (h : f x = 2) :
    preReflection x f x = -x := by
  rw [preReflection_apply, h, two_smul]; abel

lemma involutive_preReflection (h : f x = 2) :
    Involutive (preReflection x f) :=
  fun y ↦ by simp [map_sub, h, two_smul, preReflection_apply]

lemma preReflection_preReflection (g : Dual R M) (h : f x = 2) :
    preReflection (preReflection x f y) (preReflection f (Dual.eval R M x) g) =
    (preReflection x f) ∘ₗ (preReflection y g) ∘ₗ (preReflection x f) := by
  ext m
  simp only [h, preReflection_apply, mul_comm (g x) (f m), mul_two, mul_assoc, Dual.eval_apply,
    LinearMap.sub_apply, LinearMap.coe_comp, LinearMap.smul_apply, smul_eq_mul, smul_sub, sub_smul,
    smul_smul, sub_mul, comp_apply, map_sub, map_smul, add_smul]
  abel

def reflection (h : f x = 2) : M ≃ₗ[R] M :=
  { preReflection x f, (involutive_preReflection h).toPerm with }

lemma reflection_apply (h : f x = 2) :
    reflection h y = y - (f y) • x :=
  preReflection_apply x f y
