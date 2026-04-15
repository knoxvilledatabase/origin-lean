/-
Extracted from Data/Finsupp/MonomialOrder/DegLex.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! Homogeneous lexicographic monomial ordering

* `MonomialOrder.degLex`: a variant of the lexicographic ordering that first compares degrees.
For this, `σ` needs to be embedded with an ordering relation which satisfies `WellFoundedGT σ`.
(This last property is automatic when `σ` is finite).

The type synonym is `DegLex (σ →₀ ℕ)` and the two lemmas `MonomialOrder.degLex_le_iff`
and `MonomialOrder.degLex_lt_iff` rewrite the ordering as comparisons in the type `Lex (σ →₀ ℕ)`.

## References

* [Cox, Little and O'Shea, *Ideals, varieties, and algorithms*][coxlittleoshea1997]
* [Becker and Weispfenning, *Gröbner bases*][Becker-Weispfenning1993]

-/

def DegLex (α : Type*) := α

variable {α : Type*}
