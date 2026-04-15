/-
Extracted from Algebra/Lie/Weights/Linear.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lie modules with linear weights

Given a Lie module `M` over a nilpotent Lie algebra `L` with coefficients in `R`, one frequently
studies `M` via its weights. These are functions `χ : L → R` whose corresponding weight space
`LieModule.genWeightSpace M χ`, is non-trivial. If `L` is Abelian or if `R` has characteristic zero
(and `M` is finite-dimensional) then such `χ` are necessarily `R`-linear. However in general
non-linear weights do exist. For example if we take:
* `R`: the field with two elements (or indeed any perfect field of characteristic two),
* `L`: `sl₂` (this is nilpotent in characteristic two),
* `M`: the natural two-dimensional representation of `L`,

then there is a single weight and it is non-linear. (See remark following Proposition 9 of
chapter VII, §1.3 in [N. Bourbaki, Chapters 7--9](bourbaki1975b).)

We thus introduce a typeclass `LieModule.LinearWeights` to encode the fact that a Lie module does
have linear weights and provide typeclass instances in the two important cases that `L` is Abelian
or `R` has characteristic zero.

## Main definitions
* `LieModule.LinearWeights`: a typeclass encoding the fact that a given Lie module has linear
  weights, and furthermore that the weights vanish on the derived ideal.
* `LieModule.instLinearWeightsOfCharZero`: a typeclass instance encoding the fact that for an
  Abelian Lie algebra, the weights of any Lie module are linear.
* `LieModule.instLinearWeightsOfIsLieAbelian`: a typeclass instance encoding the fact that in
  characteristic zero, the weights of any finite-dimensional Lie module are linear.
* `LieModule.exists_forall_lie_eq_smul`: existence of simultaneous
  eigenvectors from existence of simultaneous generalized eigenvectors for Noetherian Lie modules
  with linear weights.

-/

open Set

variable (k R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

namespace LieModule

class LinearWeights [LieRing.IsNilpotent L] : Prop where
  map_add : ∀ χ : L → R, genWeightSpace M χ ≠ ⊥ → ∀ x y, χ (x + y) = χ x + χ y
  map_smul : ∀ χ : L → R, genWeightSpace M χ ≠ ⊥ → ∀ (t : R) x, χ (t • x) = t • χ x
  map_lie : ∀ χ : L → R, genWeightSpace M χ ≠ ⊥ → ∀ x y : L, χ ⁅x, y⁆ = 0

namespace Weight

variable [LieRing.IsNilpotent L] [LinearWeights R L M] (χ : Weight R L M)
