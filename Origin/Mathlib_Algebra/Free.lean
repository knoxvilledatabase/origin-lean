/-
Extracted from Algebra/Free.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Free constructions

## Main definitions

* `FreeMagma α`: free magma (structure with binary operation without any axioms) over alphabet `α`,
  defined inductively, with traversable instance and decidable equality.
* `MagmaAssocQuotient α`: quotient of a magma `α` by the associativity equivalence relation.
* `FreeSemigroup α`: free semigroup over alphabet `α`, defined as a structure with two fields
  `head : α` and `tail : List α` (i.e. nonempty lists), with traversable instance and decidable
  equality.
* `FreeMagmaAssocQuotientEquiv α`: isomorphism between `MagmaAssocQuotient (FreeMagma α)` and
  `FreeSemigroup α`.
* `FreeMagma.lift`: the universal property of the free magma, expressing its adjointness.
-/

universe u v l

set_option genSizeOfSpec false in

set_option genInjectivity false in

inductive FreeAddMagma (α : Type u) : Type u
  | of : α → FreeAddMagma α
  | add : FreeAddMagma α → FreeAddMagma α → FreeAddMagma α
  deriving DecidableEq

compile_inductive% FreeAddMagma

set_option genSizeOfSpec false in

set_option genInjectivity false in
