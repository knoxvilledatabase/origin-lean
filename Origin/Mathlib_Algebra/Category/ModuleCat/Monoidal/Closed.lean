/-
Extracted from Algebra/Category/ModuleCat/Monoidal/Closed.lean
Genuine: 1 of 4 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

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
  toFun f := ofHom₂ <| LinearMap.compr₂ (TensorProduct.mk R N M) ((β_ N M).hom ≫ f).hom
  invFun f := (β_ M N).hom ≫ ofHom (TensorProduct.lift f.hom₂)
  left_inv f := by
    ext : 1
    apply TensorProduct.ext'
    solve_by_elim

-- INSTANCE (free from Core): :

open MonoidalCategory
