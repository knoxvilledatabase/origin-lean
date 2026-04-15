/-
Extracted from Algebra/Star/Pi.lean
Genuine: 1 of 7 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core

/-!
# Basic Results about Star on Pi Types

This file provides basic results about the star on product types defined in
`Mathlib/Algebra/Notation/Pi/Defs.lean`.
-/

universe u v w

variable {I : Type u}

variable {f : I → Type v}

namespace Pi

-- INSTANCE (free from Core): [∀

-- INSTANCE (free from Core): [∀

-- INSTANCE (free from Core): [∀

-- INSTANCE (free from Core): [∀

-- INSTANCE (free from Core): [∀

-- INSTANCE (free from Core): {R

theorem single_star [∀ i, AddMonoid (f i)] [∀ i, StarAddMonoid (f i)] [DecidableEq I] (i : I)
    (a : f i) : Pi.single i (star a) = star (Pi.single i a) :=
  single_op (fun i => @star (f i) _) (fun _ => star_zero _) i a

open scoped ComplexConjugate
