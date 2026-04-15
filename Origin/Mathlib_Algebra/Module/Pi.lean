/-
Extracted from Algebra/Module/Pi.lean
Genuine: 1 of 4 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Pi instances for modules

This file defines instances for module and related structures on Pi Types
-/

universe u v w

variable {I : Type u}

variable {f : I → Type v}

namespace Pi

theorem _root_.IsSMulRegular.pi {α : Type*} [∀ i, SMul α <| f i] {k : α}
    (hk : ∀ i, IsSMulRegular (f i) k) : IsSMulRegular (∀ i, f i) k := fun _ _ h =>
  funext fun i => hk i (congr_fun h i :)

variable (I f)

-- INSTANCE (free from Core): module

-- INSTANCE (free from Core): Function.module

variable {I f}

-- INSTANCE (free from Core): module'

end Pi
