/-
Extracted from ModelTheory/Algebra/Ring/Basic.lean
Genuine: 7 of 18 | Dissolved: 0 | Infrastructure: 11
-/
import Origin.Core

/-!
# First-Order Language of Rings

This file defines the first-order language of rings, as well as defining instance of `Add`, `Mul`,
etc. on terms in the language.

## Main Definitions

- `FirstOrder.Language.ring` : the language of rings, with function symbols `+`, `*`, `-`, `0`, `1`
- `FirstOrder.Ring.CompatibleRing` : A class stating that a type is a `Language.ring.Structure`, and
  that this structure is the same as the structure given by the classes `Add`, `Mul`, etc. already
  on `R`.
- `FirstOrder.Ring.compatibleRingOfRing` : Given a type `R` with instances for each of the `Ring`
  operations, make a `compatibleRing` instance.

## Implementation Notes

There are implementation difficulties with the model theory of rings caused by the fact that there
are two different ways to say that `R` is a `Ring`. We can say `Ring R` or
`Language.ring.Structure R` and `Theory.ring.Model R` (The theory of rings is not implemented yet).

The recommended way to use this library is to use the hypotheses `CompatibleRing R` and `Ring R`
on any theorem that requires both a `Ring` instance and a `Language.ring.Structure` instance
in order to state the theorem. To apply such a theorem to a ring `R` with a `Ring` instance,
use the tactic `let _ := compatibleRingOfRing R`. To apply the theorem to `K`
a `Language.ring.Structure K` instance and for example an instance of `Theory.field.Model K`,
you must add local instances with definitions like `ModelTheory.Field.fieldOfModelField K` and
`FirstOrder.Ring.compatibleRingOfModelField K`.
(in `Mathlib/ModelTheory/Algebra/Field/Basic.lean`), depending on the Theory.
-/

variable {α : Type*}

namespace FirstOrder

inductive ringFunc : ℕ → Type
  | add : ringFunc 2
  | mul : ringFunc 2
  | neg : ringFunc 1
  | zero : ringFunc 0
  | one : ringFunc 0
  deriving DecidableEq

def Language.ring : Language :=
  { Functions := ringFunc
    Relations := fun _ => Empty }
  deriving IsAlgebraic

namespace Ring

open ringFunc Language

set_option backward.isDefEq.respectTransparency false in

example (n : ℕ) : DecidableEq (Language.ring.Functions n) := inferInstance

example (n : ℕ) : DecidableEq (Language.ring.Relations n) := inferInstance

abbrev addFunc : Language.ring.Functions 2 := add

abbrev mulFunc : Language.ring.Functions 2 := mul

abbrev negFunc : Language.ring.Functions 1 := neg

abbrev zeroFunc : Language.ring.Functions 0 := zero

abbrev oneFunc : Language.ring.Functions 0 := one

-- INSTANCE (free from Core): (α

{ zero := Constants.term zeroFunc }

-- INSTANCE (free from Core): (α

{ one := Constants.term oneFunc }

-- INSTANCE (free from Core): (α

{ add := addFunc.apply₂ }

-- INSTANCE (free from Core): (α

{ mul := mulFunc.apply₂ }

-- INSTANCE (free from Core): (α

{ neg := negFunc.apply₁ }

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): :
