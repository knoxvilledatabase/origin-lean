/-
Extracted from FieldTheory/AbsoluteGaloisGroup.lean
Genuine: 2 of 5 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Topology.Algebra.Group.TopologicalAbelianization

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

local notation "G_K" => absoluteGaloisGroup

noncomputable instance : Group (G_K K) := AlgEquiv.aut

noncomputable instance : TopologicalSpace (G_K K) := krullTopology K (AlgebraicClosure K)

/-! ### The topological abelianization of the absolute Galois group -/

instance absoluteGaloisGroup.commutator_closure_isNormal :
    (commutator (G_K K)).topologicalClosure.Normal :=
  Subgroup.is_normal_topologicalClosure (commutator (G_K K))

abbrev absoluteGaloisGroupAbelianization := TopologicalAbelianization (G_K K)

local notation "G_K_ab" => absoluteGaloisGroupAbelianization

end Field
