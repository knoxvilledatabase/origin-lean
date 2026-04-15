/-
Extracted from Algebra/Order/Module/PositiveLinearMap.lean
Genuine: 3 of 5 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-! # Positive linear maps

This file defines positive linear maps as a linear map that is also an order homomorphism.

## Implementation notes

We do not define `PositiveLinearMapClass` to avoid adding a class that mixes order and algebra.
One can achieve the same effect by using a combination of `LinearMapClass` and `OrderHomClass`.
We nevertheless use the namespace for lemmas using that combination of typeclasses.

## Notes

More substantial results on positive maps such as their continuity can be found in
the `Analysis/CStarAlgebra` folder.
-/

structure PositiveLinearMap (R E₁ E₂ : Type*) [Semiring R]
    [AddCommMonoid E₁] [PartialOrder E₁] [AddCommMonoid E₂] [PartialOrder E₂]
    [Module R E₁] [Module R E₂] extends E₁ →ₗ[R] E₂, E₁ →o E₂

add_decl_doc PositiveLinearMap.toOrderHom

notation:25 E " →ₚ[" R:25 "] " F:0 => PositiveLinearMap R E F

namespace PositiveLinearMapClass

variable {F R E₁ E₂ : Type*} [Semiring R]
  [AddCommMonoid E₁] [PartialOrder E₁] [AddCommMonoid E₂] [PartialOrder E₂]
  [Module R E₁] [Module R E₂] [FunLike F E₁ E₂] [LinearMapClass F R E₁ E₂]
  [OrderHomClass F E₁ E₂]

def toPositiveLinearMap (f : F) : E₁ →ₚ[R] E₂ :=
  { (f : E₁ →ₗ[R] E₂), (f : E₁ →o E₂) with }

-- INSTANCE (free from Core): instCoeToLinearMap

lemma _root_.OrderHomClass.of_addMonoidHom {F' E₁' E₂' : Type*} [FunLike F' E₁' E₂'] [AddGroup E₁']
    [LE E₁'] [AddRightMono E₁'] [AddGroup E₂'] [LE E₂'] [AddRightMono E₂']
    [AddMonoidHomClass F' E₁' E₂']
    (h : ∀ f : F', ∀ x, 0 ≤ x → 0 ≤ f x) : OrderHomClass F' E₁' E₂' where
  map_rel f a b hab := by simpa using h f (b - a) (sub_nonneg.mpr hab)

end PositiveLinearMapClass

namespace PositiveLinearMap

section general

variable {R E₁ E₂ : Type*} [Semiring R]
  [AddCommMonoid E₁] [PartialOrder E₁] [AddCommMonoid E₂] [PartialOrder E₂]
  [Module R E₁] [Module R E₂]

-- INSTANCE (free from Core): :
