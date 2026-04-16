/-
Extracted from Algebra/Algebra/Pi.lean
Genuine: 5 | Conflates: 0 | Dissolved: 0 | Infrastructure: 9
-/
import Origin.Core
import Mathlib.Algebra.Algebra.Equiv

noncomputable section

/-!
# The R-algebra structure on families of R-algebras

The R-algebra structure on `∀ i : I, A i` when each `A i` is an R-algebra.

## Main definitions

* `Pi.algebra`
* `Pi.evalAlgHom`
* `Pi.constAlgHom`
-/

universe u v w

namespace Pi

variable {I : Type u}

variable {R : Type*}

variable {f : I → Type v}

variable (x y : ∀ i, f i) (i : I)

variable (I f)

instance algebra {r : CommSemiring R} [s : ∀ i, Semiring (f i)] [∀ i, Algebra R (f i)] :
    Algebra R (∀ i : I, f i) :=
  { (Pi.ringHom fun i => algebraMap R (f i) : R →+* ∀ i : I, f i) with
    commutes' := fun a f => by ext; simp [Algebra.commutes]
    smul_def' := fun a f => by ext; simp [Algebra.smul_def] }

variable {I} (R)

@[simps!]
def algHom [CommSemiring R] [s : ∀ i, Semiring (f i)] [∀ i, Algebra R (f i)]
    {A : Type*} [Semiring A] [Algebra R A] (g : ∀ i, A →ₐ[R] f i) :
      A →ₐ[R] ∀ i, f i where
  __ := Pi.ringHom fun i ↦ (g i).toRingHom
  commutes' r := by ext; simp

@[simps]
def evalAlgHom {_ : CommSemiring R} [∀ i, Semiring (f i)] [∀ i, Algebra R (f i)] (i : I) :
    (∀ i, f i) →ₐ[R] f i :=
  { Pi.evalRingHom f i with
    toFun := fun f => f i
    commutes' := fun _ => rfl }

variable (A B : Type*) [CommSemiring R] [Semiring B] [Algebra R B]

@[simps]
def constAlgHom : B →ₐ[R] A → B :=
  { Pi.constRingHom A B with
    toFun := Function.const _
    commutes' := fun _ => rfl }

end Pi

instance Function.algebra {R : Type*} (I : Type*) (A : Type*) [CommSemiring R] [Semiring A]
    [Algebra R A] : Algebra R (I → A) :=
  Pi.algebra _ _

namespace AlgHom

variable {R : Type u} {A : Type v} {B : Type w} {I : Type*}

variable [CommSemiring R] [Semiring A] [Semiring B]

variable [Algebra R A] [Algebra R B]

@[simps]
protected def compLeft (f : A →ₐ[R] B) (I : Type*) : (I → A) →ₐ[R] I → B :=
  { f.toRingHom.compLeft I with
    toFun := fun h => f ∘ h
    commutes' := fun c => by
      ext
      exact f.commutes' c }

end AlgHom

namespace AlgEquiv

@[simps apply]
def piCongrRight {R ι : Type*} {A₁ A₂ : ι → Type*} [CommSemiring R] [∀ i, Semiring (A₁ i)]
    [∀ i, Semiring (A₂ i)] [∀ i, Algebra R (A₁ i)] [∀ i, Algebra R (A₂ i)]
    (e : ∀ i, A₁ i ≃ₐ[R] A₂ i) : (∀ i, A₁ i) ≃ₐ[R] ∀ i, A₂ i :=
  { @RingEquiv.piCongrRight ι A₁ A₂ _ _ fun i => (e i).toRingEquiv with
    toFun := fun x j => e j (x j)
    invFun := fun x j => (e j).symm (x j)
    commutes' := fun r => by
      ext i
      simp }

end AlgEquiv
