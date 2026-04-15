/-
Extracted from Data/Fin/Tuple/Basic.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Operation on tuples

We interpret maps `∀ i : Fin n, α i` as `n`-tuples of elements of possibly varying type `α i`,
`(α 0, …, α (n-1))`. A particular case is `Fin n → α` of elements with all the same type.
In this case when `α i` is a constant map, then tuples are isomorphic (but not definitionally equal)
to `Vector`s.

## Main declarations

There are three (main) ways to consider `Fin n` as a subtype of `Fin (n + 1)`, hence three (main)
ways to move between tuples of length `n` and of length `n + 1` by adding/removing an entry.

### Adding at the start

* `Fin.succ`: Send `i : Fin n` to `i + 1 : Fin (n + 1)`. This is defined in Core.
* `Fin.cases`: Induction/recursion principle for `Fin`: To prove a property/define a function for
  all `Fin (n + 1)`, it is enough to prove/define it for `0` and for `i.succ` for all `i : Fin n`.
  This is defined in Core.
* `Fin.cons`: Turn a tuple `f : Fin n → α` and an entry `a : α` into a tuple
  `Fin.cons a f : Fin (n + 1) → α` by adding `a` at the start. In general, tuples can be dependent
  functions, in which case `f : ∀ i : Fin n, α i.succ` and `a : α 0`. This is a special case of
  `Fin.cases`.
* `Fin.tail`: Turn a tuple `f : Fin (n + 1) → α` into a tuple `Fin.tail f : Fin n → α` by forgetting
  the start. In general, tuples can be dependent functions,
  in which case `Fin.tail f : ∀ i : Fin n, α i.succ`.

### Adding at the end

* `Fin.castSucc`: Send `i : Fin n` to `i : Fin (n + 1)`. This is defined in Core.
* `Fin.lastCases`: Induction/recursion principle for `Fin`: To prove a property/define a function
  for all `Fin (n + 1)`, it is enough to prove/define it for `last n` and for `i.castSucc` for all
  `i : Fin n`. This is defined in Core.
* `Fin.snoc`: Turn a tuple `f : Fin n → α` and an entry `a : α` into a tuple
  `Fin.snoc f a : Fin (n + 1) → α` by adding `a` at the end. In general, tuples can be dependent
  functions, in which case `f : ∀ i : Fin n, α i.castSucc` and `a : α (last n)`. This is a
  special case of `Fin.lastCases`.
* `Fin.init`: Turn a tuple `f : Fin (n + 1) → α` into a tuple `Fin.init f : Fin n → α` by forgetting
  the end. In general, tuples can be dependent functions,
  in which case `Fin.init f : ∀ i : Fin n, α i.castSucc`.

### Adding in the middle

For a **pivot** `p : Fin (n + 1)`,
* `Fin.succAbove`: Send `i : Fin n` to
  * `i : Fin (n + 1)` if `i < p`,
  * `i + 1 : Fin (n + 1)` if `p ≤ i`.
* `Fin.succAboveCases`: Induction/recursion principle for `Fin`: To prove a property/define a
  function for all `Fin (n + 1)`, it is enough to prove/define it for `p` and for `p.succAbove i`
  for all `i : Fin n`.
* `Fin.insertNth`: Turn a tuple `f : Fin n → α` and an entry `a : α` into a tuple
  `Fin.insertNth f a : Fin (n + 1) → α` by adding `a` in position `p`. In general, tuples can be
  dependent functions, in which case `f : ∀ i : Fin n, α (p.succAbove i)` and `a : α p`. This is a
  special case of `Fin.succAboveCases`.
* `Fin.removeNth`: Turn a tuple `f : Fin (n + 1) → α` into a tuple `Fin.removeNth p f : Fin n → α`
  by forgetting the `p`-th value. In general, tuples can be dependent functions,
  in which case `Fin.removeNth f : ∀ i : Fin n, α (succAbove p i)`.

`p = 0` means we add at the start. `p = last n` means we add at the end.

### Miscellaneous

* `Fin.find p h` : returns the first index `i : Fin n` where `p i` is satisfied given the
  hypothesis that `h : ∃ i, p i`.
* `Fin.append a b` : append two tuples.
* `Fin.repeat n a` : repeat a tuple `n` times.

-/

assert_not_exists Monoid

universe u v

namespace Fin

variable {m n : ℕ}

open Function

section Tuple

example (α : Fin 0 → Sort u) : Unique (∀ i : Fin 0, α i) := by infer_instance

theorem tuple0_le {α : Fin 0 → Type*} [∀ i, Preorder (α i)] (f g : ∀ i, α i) : f ≤ g :=
  finZeroElim

variable {α : Fin (n + 1) → Sort u} (x : α 0) (q : ∀ i, α i) (p : ∀ i : Fin n, α i.succ) (i : Fin n)
  (y : α i.succ) (z : α 0)

def tail (q : ∀ i, α i) : ∀ i : Fin n, α i.succ := fun i ↦ q i.succ

def cons (x : α 0) (p : ∀ i : Fin n, α i.succ) : ∀ i, α i := fun j ↦ Fin.cases x p j
