/-
Extracted from Computability/MyhillNerode.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Myhill–Nerode theorem

This file proves the Myhill–Nerode theorem using left quotients.

Given a language `L` and a word `x`, the *left quotient* of `L` by `x` is the set of suffixes `y`
such that `x ++ y` is in `L`. The *Myhill–Nerode theorem* shows that each left quotient, in fact,
corresponds to the state of an automaton that matches `L`, and that `L` is regular if and only if
there are finitely many such states.

## References

* <https://en.wikipedia.org/wiki/Syntactic_monoid#Myhill%E2%80%93Nerode_theorem>
-/

universe u v

variable {α : Type u} {σ : Type v} {L : Language α}

namespace Language

variable (L) in

def leftQuotient (x : List α) : Language α := { y | x ++ y ∈ L }

variable (L) in
