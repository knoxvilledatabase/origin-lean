/-
Extracted from RingTheory/Kaehler/TensorProduct.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Kähler differential module under base change

## Main results
- `KaehlerDifferential.tensorKaehlerEquivBase`: `(S ⊗[R] Ω[A⁄R]) ≃ₗ[S] Ω[B⁄S]` for `B = S ⊗[R] A`.
- `KaehlerDifferential.tensorKaehlerEquiv`: `(B ⊗[A] Ω[A⁄R]) ≃ₗ[B] Ω[B⁄S]` for `B = S ⊗[R] A`.
- `KaehlerDifferential.isLocalizedModule_of_isLocalizedModule`:
  `Ω[Aₚ/Rₚ]` is the localization of `Ω[A/R]` at `p`.

-/

variable (R S A B : Type*) [CommRing R] [CommRing S] [Algebra R S] [CommRing A] [CommRing B]

variable [Algebra R A] [Algebra R B]

variable [Algebra A B] [Algebra S B] [IsScalarTower R A B] [IsScalarTower R S B]

open TensorProduct

attribute [local instance] SMulCommClass.of_commMonoid

attribute [local irreducible] KaehlerDifferential

namespace KaehlerDifferential

noncomputable

abbrev mulActionBaseChange : MulAction A (S ⊗[R] Ω[A⁄R]) :=
  (TensorProduct.comm R S Ω[A⁄R]).toEquiv.mulAction A

attribute [local instance] mulActionBaseChange
