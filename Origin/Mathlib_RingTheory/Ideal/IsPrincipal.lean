/-
Extracted from RingTheory/Ideal/IsPrincipal.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Principal Ideals

This file deals with the set of principal ideals of a `CommRing R`.

## Main definitions and results

* `Ideal.isPrincipalSubmonoid`: the submonoid of `Ideal R` formed by the principal ideals of `R`.

* `Ideal.isPrincipalNonZeroDivisorSubmonoid`: the submonoid of `(Ideal R)⁰` formed by the
  non-zero-divisors principal ideals of `R`.

* `Ideal.associatesMulEquivIsPrincipal`: the `MulEquiv` between the monoid of `Associates R` and
  the submonoid of principal ideals of `R`.

* `Ideal.associatesNonZeroDivisorsMulEquivIsPrincipal`: the `MulEquiv` between the monoid of
  `Associates R⁰` and the submonoid of non-zero-divisors principal ideals of `R`.
-/

variable {R : Type*} [CommRing R]

namespace Ideal

open Submodule Associates

open scoped nonZeroDivisors

variable (R) in

def isPrincipalSubmonoid : Submonoid (Ideal R) where
  carrier := {I | IsPrincipal I}
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x * y, span_singleton_mul_span_singleton x y⟩
  one_mem' := ⟨1, one_eq_span⟩

theorem span_singleton_mem_isPrincipalSubmonoid (a : R) :
    span {a} ∈ isPrincipalSubmonoid R := mem_isPrincipalSubmonoid_iff.mpr ⟨a, rfl⟩

variable (R) in

def isPrincipalNonZeroDivisorsSubmonoid : Submonoid (Ideal R)⁰ where
  carrier := {I | IsPrincipal I.val}
  mul_mem' := by
    rintro ⟨_, _⟩ ⟨_, _⟩ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x * y, by
      simp_rw [Submonoid.mk_mul_mk, submodule_span_eq, span_singleton_mul_span_singleton]⟩
  one_mem' := ⟨1, by simp⟩

variable [IsDomain R]

variable (R) in

noncomputable def associatesEquivIsPrincipal :
    Associates R ≃ {I : Ideal R // IsPrincipal I} where
  toFun := _root_.Quotient.lift (fun x ↦ ⟨span {x}, x, rfl⟩)
    (fun _ _ _ ↦ by simpa [span_singleton_eq_span_singleton])
  invFun I := .mk I.2.generator
  left_inv := Quotient.ind fun _ ↦ by simpa [Quotient.eq] using
    Ideal.span_singleton_eq_span_singleton.mp (@Ideal.span_singleton_generator _ _ _ ⟨_, rfl⟩)
  right_inv I := by simp only [_root_.Quotient.lift_mk, span_singleton_generator, Subtype.coe_eta]
