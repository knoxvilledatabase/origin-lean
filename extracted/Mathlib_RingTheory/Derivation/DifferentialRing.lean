/-
Extracted from RingTheory/Derivation/DifferentialRing.lean
Genuine: 8 | Conflates: 0 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.RingTheory.Derivation.Basic

noncomputable section

/-!
# Differential and Algebras

This file defines derivations from a commutative ring to itself as a typeclass, which lets us
use the x′ notation for the derivative of x.
-/

class Differential (R : Type*) [CommRing R] where
  /-- The `Derivation` associated with the ring. -/
  deriv : Derivation ℤ R R

scoped[Differential] postfix:max "′" => Differential.deriv

open scoped Differential

open Lean PrettyPrinter Delaborator SubExpr in

@[delab app.DFunLike.coe]
def delabDeriv : Delab := do
  let e ← getExpr
  guard <| e.isAppOfArity' ``DFunLike.coe 6
  guard <| (e.getArg!' 4).isAppOf' ``Differential.deriv
  let arg ← withAppArg delab
  `($arg′)

class DifferentialAlgebra (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Differential A] [Differential B] : Prop where
  deriv_algebraMap : ∀ a : A, (algebraMap A B a)′ = algebraMap A B a′

export DifferentialAlgebra (deriv_algebraMap)

@[norm_cast]
lemma algebraMap.coe_deriv {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Differential A] [Differential B] [DifferentialAlgebra A B] (a : A) :
    (a′ : A) = (a : B)′ :=
  (DifferentialAlgebra.deriv_algebraMap _).symm

class Differential.ContainConstants (A B : Type*) [CommRing A] [CommRing B]
    [Algebra A B] [Differential B] : Prop where
  /-- If the derivative of x is 0, then it's in the range of `algberaMap A B`. -/
  protected mem_range_of_deriv_eq_zero {x : B} (h : x′ = 0) : x ∈ (algebraMap A B).range

lemma mem_range_of_deriv_eq_zero (A : Type*) {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Differential B] [Differential.ContainConstants A B] {x : B} (h : x′ = 0) :
    x ∈ (algebraMap A B).range :=
  Differential.ContainConstants.mem_range_of_deriv_eq_zero h

instance (A : Type*) [CommRing A] [Differential A] : DifferentialAlgebra A A where
  deriv_algebraMap _ := rfl

instance (A : Type*) [CommRing A] [Differential A] : Differential.ContainConstants A A where
  mem_range_of_deriv_eq_zero {x} _ := ⟨x, rfl⟩

@[reducible]
def Differential.equiv {R R₂ : Type*} [CommRing R] [CommRing R₂] [Differential R₂]
    (h : R ≃+* R₂) : Differential R :=
  ⟨Derivation.mk' (h.symm.toAddMonoidHom.toIntLinearMap ∘ₗ
    Differential.deriv.toLinearMap ∘ₗ h.toAddMonoidHom.toIntLinearMap) (by simp)⟩

lemma DifferentialAlgebra.equiv {A : Type*} [CommRing A] [Differential A]
    {R R₂ : Type*} [CommRing R] [CommRing R₂] [Differential R₂] [Algebra A R]
    [Algebra A R₂] [DifferentialAlgebra A R₂] (h : R ≃ₐ[A] R₂) :
    letI := Differential.equiv h.toRingEquiv
    DifferentialAlgebra A R :=
  letI := Differential.equiv h.toRingEquiv
  ⟨fun a ↦ by
    change (LinearMap.comp ..) _ = _
    simp only [AlgEquiv.toRingEquiv_eq_coe, RingHom.toAddMonoidHom_eq_coe,
      RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom, LinearMap.coe_comp,
      AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.coe_coe, RingHom.coe_coe, Derivation.coeFn_coe,
      Function.comp_apply, AlgEquiv.commutes, deriv_algebraMap]
    apply h.symm.commutes⟩
