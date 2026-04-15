/-
Extracted from RingTheory/Ideal/Maps.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Maps on modules and ideals

Main definitions include `Ideal.map`, `Ideal.comap`, `RingHom.ker`, `Module.annihilator`
and `Submodule.annihilator`.
-/

assert_not_exists Module.Basis -- See `RingTheory.Ideal.Basis`

  Submodule.hasQuotient -- See `RingTheory.Ideal.Quotient.Operations`

universe u v w x

open Pointwise

namespace Ideal

section MapAndComap

variable {R : Type u} {S : Type v}

section Semiring

variable {F : Type*} [Semiring R] [Semiring S]

variable [FunLike F R S]

variable (f : F)

variable {I J : Ideal R} {K L : Ideal S}

def map (I : Ideal R) : Ideal S :=
  span (f '' I)

def comap [RingHomClass F R S] (I : Ideal S) : Ideal R where
  carrier := f ⁻¹' I
  add_mem' {x y} hx hy := by
    simp only [Set.mem_preimage, SetLike.mem_coe, map_add f] at hx hy ⊢
    exact add_mem hx hy
  zero_mem' := by simp only [Set.mem_preimage, map_zero, SetLike.mem_coe, Submodule.zero_mem]
  smul_mem' c x hx := by
    simp only [smul_eq_mul, Set.mem_preimage, map_mul, SetLike.mem_coe] at *
    exact mul_mem_left I _ hx
