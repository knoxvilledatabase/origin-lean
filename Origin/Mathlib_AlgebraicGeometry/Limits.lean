/-
Extracted from AlgebraicGeometry/Limits.lean
Genuine: 2 of 8 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core

/-!
# (Co)Limits of Schemes

We construct various limits and colimits in the category of schemes.

* The existence of fibred products was shown in `Mathlib/AlgebraicGeometry/Pullbacks.lean`.
* `Spec ℤ` is the terminal object.
* The preceding two results imply that `Scheme` has all finite limits.
* The empty scheme is the (strict) initial object.
* The disjoint union is the coproduct of a family of schemes, and the forgetful functor to
  `LocallyRingedSpace` and `TopCat` preserves them.

## TODO

* Spec preserves finite coproducts.

-/

suppress_compilation

universe u v

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

attribute [local instance] Opposite.small

namespace AlgebraicGeometry

noncomputable def specZIsTerminal : IsTerminal (Spec <| .of ℤ) :=
  @IsTerminal.isTerminalObj _ _ _ _ Scheme.Spec _ inferInstance
    (terminalOpOfInitial CommRingCat.zIsInitial)

noncomputable def specULiftZIsTerminal : IsTerminal (Spec <| .of <| ULift.{u} ℤ) :=
  @IsTerminal.isTerminalObj _ _ _ _ Scheme.Spec _ inferInstance
    (terminalOpOfInitial CommRingCat.isInitial)

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): (X

-- INSTANCE (free from Core): {X

-- INSTANCE (free from Core): {X

section Initial
