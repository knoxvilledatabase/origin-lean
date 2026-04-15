/-
Extracted from FieldTheory/AbsoluteGaloisGroup.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The topological abelianization of the absolute Galois group.

We define the absolute Galois group of a field `K` and its topological abelianization.

## Main definitions
- `Field.absoluteGaloisGroup` : The Galois group of the field extension `K^al/K`, where `K^al` is an
  algebraic closure of `K`.
- `Field.absoluteGaloisGroupAbelianization` : The topological abelianization of
  `Field.absoluteGaloisGroup K`, that is, the quotient of `Field.absoluteGaloisGroup K` by the
  topological closure of its commutator subgroup.

## Main results
- `Field.absoluteGaloisGroup.commutator_closure_isNormal` : the topological closure of the
  commutator of `absoluteGaloisGroup` is a normal subgroup.

## Tags
field, algebraic closure, galois group, abelianization

-/

namespace Field

variable (K : Type*) [Field K]

/-! ### The absolute Galois group -/

def absoluteGaloisGroup := AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K

deriving Group, TopologicalSpace, IsTopologicalGroup

add_decl_doc instTopologicalSpaceAbsoluteGaloisGroup

local notation "G_K" => absoluteGaloisGroup

/-! ### The topological abelianization of the absolute Galois group -/

-- INSTANCE (free from Core): absoluteGaloisGroup.commutator_closure_isNormal

abbrev absoluteGaloisGroupAbelianization := TopologicalAbelianization (G_K K)

local notation "G_K_ab" => absoluteGaloisGroupAbelianization

end Field
