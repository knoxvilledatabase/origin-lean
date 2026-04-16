/-
Extracted from Algebra/Category/ModuleCat/Monoidal/Closed.lean
Genuine: 2 | Conflates: 0 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core
import Mathlib.CategoryTheory.Closed.Monoidal
import Mathlib.CategoryTheory.Linear.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric

noncomputable section

/-!
# The monoidal closed structure on `Module R`.
-/

universe v w x u

open CategoryTheory Opposite

namespace ModuleCat

variable {R : Type u} [CommRing R]

def monoidalClosedHomEquiv (M N P : ModuleCat.{u} R) :
    ((MonoidalCategory.tensorLeft M).obj N ⟶ P) ≃
      (N ⟶ ((linearCoyoneda R (ModuleCat R)).obj (op M)).obj P) where
  toFun f := LinearMap.compr₂ (TensorProduct.mk R N M) ((β_ N M).hom ≫ f)
  invFun f := (β_ M N).hom ≫ TensorProduct.lift f
  left_inv f := by
    apply TensorProduct.ext'
    intro m n
    -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
    erw [coe_comp]
    rw [Function.comp_apply]
    -- This used to be `rw` and was longer (?), but we need `erw` after https://github.com/leanprover/lean4/pull/2644
    erw [MonoidalCategory.braiding_hom_apply, TensorProduct.lift.tmul]
  right_inv _ := rfl

instance : MonoidalClosed (ModuleCat.{u} R) where
  closed M :=
    { rightAdj := (linearCoyoneda R (ModuleCat.{u} R)).obj (op M)
      adj := Adjunction.mkOfHomEquiv
            { homEquiv := fun N P => monoidalClosedHomEquiv M N P
              -- Porting note: this proof was automatic in mathlib3
              homEquiv_naturality_left_symm := by
                intros
                apply TensorProduct.ext'
                intro m n
                rfl } }

open MonoidalCategory

@[simp]
theorem monoidalClosed_uncurry
    {M N P : ModuleCat.{u} R} (f : N ⟶ M ⟶[ModuleCat.{u} R] P) (x : M) (y : N) :
    MonoidalClosed.uncurry f (x ⊗ₜ[R] y) =
      @DFunLike.coe _ _ _ LinearMap.instFunLike (f y) x :=
  rfl

theorem ihom_ev_app (M N : ModuleCat.{u} R) :
    (ihom.ev M).app N = TensorProduct.uncurry _ _ _ _ LinearMap.id.flip := by
  rw [← MonoidalClosed.uncurry_id_eq_ev]
  apply TensorProduct.ext'
  apply monoidalClosed_uncurry

end ModuleCat
