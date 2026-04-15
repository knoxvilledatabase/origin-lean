/-
Extracted from Data/Finsupp/Basic.lean
Genuine: 1 of 2 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-!
# Miscellaneous definitions, lemmas, and constructions using finsupp

## Main declarations

* `Finsupp.graph`: the finset of input and output pairs with non-zero outputs.
* `Finsupp.mapRange.equiv`: `Finsupp.mapRange` as an equiv.
* `Finsupp.mapDomain`: maps the domain of a `Finsupp` by a function and by summing.
* `Finsupp.comapDomain`: postcomposition of a `Finsupp` with a function injective on the preimage
  of its support.
* `Finsupp.filter`: `filter p f` is the finitely supported function that is `f a` if `p a` is true
  and 0 otherwise.
* `Finsupp.frange`: the image of a finitely supported function on its support.
* `Finsupp.subtype_domain`: the restriction of a finitely supported function `f` to a subtype.

## Implementation notes

This file is a `noncomputable theory` and uses classical logic throughout.

## TODO

* Expand the list of definitions and important lemmas to the module docstring.

-/

noncomputable section

open Finset Function

variable {α β γ ι M N P G H R S : Type*}

namespace Finsupp

/-! ### Declarations about `graph` -/

section Graph

variable [Zero M]

def graph (f : α →₀ M) : Finset (α × M) :=
  f.support.map ⟨fun a => Prod.mk a (f a), fun _ _ h => (Prod.mk.inj h).1⟩

-- DISSOLVED: mk_mem_graph_iff
