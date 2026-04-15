/-
Extracted from Combinatorics/Matroid/Loop.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Matroid loops and coloops

## Loops
A 'loop' of a matroid `M` is an element `e` satisfying one of the following equivalent conditions:
* `e ∈ M.closure ∅`;
* `{e}` is dependent in `M`;
* `{e}` is a circuit of `M`;
* no base of `M` contains `e`.

In many mathematical contexts, loops can be thought of as 'trivial' or 'zero' elements;
For linearly representable matroids, they correspond to the zero vector,
and for graphic matroids, they correspond to edges incident with just one vertex (aka 'loops').
As trivial as they are, loops can be created from matroids with no loops by taking minors or duals,
so in many contexts it is unreasonable to simply forbid loops from appearing.
For `M : Matroid α`, this file defines a set `Matroid.loops M : Set α`,
as well as predicates `Matroid.IsLoop M : α → Prop` and `Matroid.IsNonloop M : α → Prop`,
and provides API for interacting with them.

## Coloops
The dual notion of a loop is a 'coloop'. Geometrically, these can be thought of elements that are
skew to the remainder of the matroid. Coloops in graphic matroids are 'bridge' edges of the graph,
and coloops in linearly representable matroids are vectors not spanned by the other vectors
in the matroid.
Coloops also have many equivalent definitions in abstract matroid language;
a coloop is an element of `M.E` if any of the following equivalent conditions holds :
* `e` is a loop of `M✶`;
* `{e}` is a cocircuit of `M`;
* `e` is in no circuit of `M`;
* `e` is in every base of `M`;
* for all `X ⊆ M.E`, `e ∈ X ↔ e ∈ M.closure X`,
* `M.E \ {e}` is nonspanning.

## Main Declarations
For `M` : Matroid `α`:
* `M.loops` is the set `M.closure ∅`.
* `M.IsLoop e` means that `e : α` is a loop of `M`, defined as the statement `e ∈ M.loops`.
* `M.isLoop_tfae` gives a number of properties that are equivalent to `IsLoop`.
* `M.IsNonloop e` means that `e ∈ M.E`, but `e` is not a loop of `M`.
* `M.IsColoop e ` means that `e` is a loop of `M✶`.
* `M.coloops` is the set of coloops of `M✶`.
* `M.isColoop_tfae` gives a number of properties that are equivalent to `IsColoop`.
* `M.Loopless` is a typeclass meaning `M` has no loops.
* `M.removeLoops` is the matroid obtained from `M` by restricting to its set of nonloop elements.
-/

variable {α β : Type*} {M N : Matroid α} {e f : α} {F X C I : Set α}

open Set

namespace Matroid

def loops (M : Matroid α) := M.closure ∅
