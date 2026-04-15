/-
Extracted from Analysis/Normed/Unbundled/AlgebraNorm.lean
Genuine: 3 of 7 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Algebra norms

We define algebra norms and multiplicative algebra norms.

## Main Definitions
* `AlgebraNorm` : an algebra norm on an `R`-algebra `S` is a ring norm on `S` compatible with
  the action of `R`.
* `MulAlgebraNorm` : a multiplicative algebra norm on an `R`-algebra `S` is a multiplicative
  ring norm on `S` compatible with the action of `R`.

## Tags

norm, algebra norm
-/

structure AlgebraNorm (R : Type*) [SeminormedCommRing R] (S : Type*) [Ring S] [Algebra R S] extends
  RingNorm S, Seminorm R S

attribute [nolint docBlame] AlgebraNorm.toSeminorm AlgebraNorm.toRingNorm

-- INSTANCE (free from Core): (K

class AlgebraNormClass (F : Type*) (R : outParam <| Type*) [SeminormedCommRing R]
    (S : outParam <| Type*) [Ring S] [Algebra R S] [FunLike F S ℝ] : Prop
    extends RingNormClass F S ℝ, SeminormClass F R S

namespace AlgebraNorm

variable {R : Type*} [SeminormedCommRing R] {S : Type*} [Ring S] [Algebra R S] {f : AlgebraNorm R S}

def toRingSeminorm' (f : AlgebraNorm R S) : RingSeminorm S :=
  f.toRingNorm.toRingSeminorm

-- INSTANCE (free from Core): :

set_option linter.style.whitespace false in -- manual alignment is not recognised

-- INSTANCE (free from Core): algebraNormClass
