/-
Extracted from Algebra/AddConstMap/Equiv.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Equivalences conjugating `(· + a)` to `(· + b)`

In this file we define `AddConstEquiv G H a b` (notation: `G ≃+c[a, b] H`)
to be the type of equivalences such that `∀ x, f (x + a) = f x + b`.

We also define the corresponding typeclass and prove some basic properties.
-/

assert_not_exists Finset

open Function

open scoped AddConstMap

structure AddConstEquiv (G H : Type*) [Add G] [Add H] (a : G) (b : H)
  extends G ≃ H, G →+c[a, b] H

add_decl_doc AddConstEquiv.toEquiv

add_decl_doc AddConstEquiv.toAddConstMap
