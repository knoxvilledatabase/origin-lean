/-
Extracted from Algebra/Category/ModuleCat/Monoidal/Symmetric.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The symmetric monoidal structure on `Module R`.
-/

universe v w x u

open CategoryTheory MonoidalCategory

namespace SemimoduleCat

variable {R : Type u} [CommSemiring R]

def braiding (M N : SemimoduleCat.{u} R) : M ⊗ N ≅ N ⊗ M :=
  LinearEquiv.toModuleIsoₛ (TensorProduct.comm R M N)

namespace MonoidalCategory
