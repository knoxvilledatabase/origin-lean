/-
Extracted from RingTheory/OrderOfVanishing/Noetherian.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Order of vanishing in Noetherian rings.

In this file we define various properties of the order of vanishing in Noetherian rings, including
 some API for computing the order of vanishing in discrete valuation rings.
-/

variable {R : Type*} [CommRing R]

namespace Ring

section NoetherianDimLEOne

variable {R : Type*} [CommRing R]

variable [IsNoetherianRing R] [Ring.KrullDimLE 1 R]

variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

open scoped nonZeroDivisors

noncomputable

def ordMonoidHom : R⁰ →* Multiplicative ℕ where
  toFun x := .ofAdd <| (Ring.ord R x).toNat
  map_one' := by simp [OneMemClass.coe_one, isUnit_one, ord_of_isUnit]
  map_mul' x y := by simp [ord_mul, ENat.toNat_add (ord_ne_top x.2) (ord_ne_top y.2)]
