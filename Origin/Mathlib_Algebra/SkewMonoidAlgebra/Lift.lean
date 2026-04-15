/-
Extracted from Algebra/SkewMonoidAlgebra/Lift.lean
Genuine: 3 of 5 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Lemmas about different kinds of "lifts" to `SkewMonoidAlgebra`.
-/

noncomputable section

namespace SkewMonoidAlgebra

variable {k G H : Type*}

section lift

variable [CommSemiring k] [Monoid G] [Monoid H]

variable {A B : Type*} [Semiring A] [Algebra k A] [Semiring B] [Algebra k B]

def liftNCAlgHom [MulSemiringAction G A] [SMulCommClass G k A] (f : A →ₐ[k] B)
    (g : G →* B) (h_comm : ∀ {x y}, (f (y • x)) * g y = (g y) * (f x)) :
    SkewMonoidAlgebra A G →ₐ[k] B where
  __ := liftNCRingHom (f : A →+* B) g h_comm
  commutes' := by simp [liftNCRingHom]

variable [MulSemiringAction G k] [SMulCommClass G k k]

variable (k G A)

def lift : (G →* A) ≃ (AlgHom k (SkewMonoidAlgebra k G) A) where
  invFun f := (f : SkewMonoidAlgebra k G →* A).comp (of k G)
  toFun F := by
    apply liftNCAlgHom (Algebra.ofId k A) F
    simp_rw [show ∀ (g : G) (r : k), g • r = r by
        exact fun _ _ ↦ smul_algebraMap _ (algebraMap k k _)]
    exact Algebra.commutes _ _
  left_inv f := by
    ext
    simp [liftNCAlgHom, liftNCRingHom]
  right_inv F := by
    ext
    simp [liftNCAlgHom, liftNCRingHom]

variable {k G A}

theorem lift_apply (F : G →* A) (f : SkewMonoidAlgebra k G) :
    lift k G A F f = f.sum fun a b ↦ b • F a := by simp [lift_apply', Algebra.smul_def]
