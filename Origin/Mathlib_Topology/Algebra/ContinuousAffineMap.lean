/-
Extracted from Topology/Algebra/ContinuousAffineMap.lean
Genuine: 3 of 7 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Continuous affine maps.

This file defines a type of bundled continuous affine maps.

## Main definitions:

* `ContinuousAffineMap`

## Notation:

We introduce the notation `P →ᴬ[R] Q` for `ContinuousAffineMap R P Q` (not to be confused with the
notation `A →A[R] B` for `ContinuousAlgHom`). Note that this is parallel to the notation `E →L[R] F`
for `ContinuousLinearMap R E F`.
-/

structure ContinuousAffineMap (R : Type*) {V W : Type*} (P Q : Type*) [Ring R] [AddCommGroup V]
  [Module R V] [TopologicalSpace P] [AddTorsor V P] [AddCommGroup W] [Module R W]
  [TopologicalSpace Q] [AddTorsor W Q] extends P →ᵃ[R] Q where
  cont : Continuous toFun

notation:25 P " →ᴬ[" R "] " Q => ContinuousAffineMap R P Q

namespace ContinuousAffineMap

variable {R V W P Q : Type*} [Ring R]

variable [AddCommGroup V] [Module R V] [TopologicalSpace P] [AddTorsor V P]

variable [AddCommGroup W] [Module R W] [TopologicalSpace Q] [AddTorsor W Q]

-- INSTANCE (free from Core): :

attribute [coe] ContinuousAffineMap.toAffineMap

theorem toAffineMap_injective {f g : P →ᴬ[R] Q} (h : (f : P →ᵃ[R] Q) = (g : P →ᵃ[R] Q)) :
    f = g := by
  cases f
  cases g
  congr

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

theorem coe_injective : @Function.Injective (P →ᴬ[R] Q) (P → Q) (⇑) :=
  DFunLike.coe_injective
