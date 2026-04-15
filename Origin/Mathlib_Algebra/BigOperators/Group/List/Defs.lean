/-
Extracted from Algebra/BigOperators/Group/List/Defs.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Sums and products from lists

This file provides basic definitions for `List.prod`, `List.sum`,
which calculate the product and sum of elements of a list
and `List.alternatingProd`, `List.alternatingSum`, their alternating counterparts.
-/

variable {ι M N : Type*}

namespace List

section Defs

set_option linter.existingAttributeWarning false in

attribute [to_additive existing] prod prod_nil prod_cons prod_one_cons prod_append prod_concat

  prod_flatten prod_eq_foldl

def alternatingSum {G : Type*} [Zero G] [Add G] [Neg G] : List G → G
  | [] => 0
  | g :: [] => g
  | g :: h :: t => g + -h + alternatingSum t
