/-
Extracted from Data/Fin/Tuple/Take.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Take operations on tuples

We define the `take` operation on `n`-tuples, which restricts a tuple to its first `m` elements.

* `Fin.take`: Given `h : m ≤ n`, `Fin.take m h v` for an `n`-tuple `v = (v 0, ..., v (n - 1))` is
  the `m`-tuple `(v 0, ..., v (m - 1))`.
-/

namespace Fin

open Function

variable {n : ℕ} {α : Fin n → Sort*}

section Take

def take (m : ℕ) (h : m ≤ n) (v : (i : Fin n) → α i) : (i : Fin m) → α (castLE h i) :=
  fun i ↦ v (castLE h i)
