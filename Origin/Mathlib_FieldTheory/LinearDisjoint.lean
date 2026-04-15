/-
Extracted from FieldTheory/LinearDisjoint.lean
Genuine: 16 of 17 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!

# Linearly disjoint fields

This file contains basics about the linearly disjoint fields.
We adapt the definitions in <https://en.wikipedia.org/wiki/Linearly_disjoint>.
See the file `Mathlib/LinearAlgebra/LinearDisjoint.lean`
and `Mathlib/RingTheory/LinearDisjoint.lean` for details.

## Main definitions

- `IntermediateField.LinearDisjoint`: an intermediate field `A` of `E / F`
  and an abstract field `L` between `E / F`
  (as a special case, two intermediate fields) are linearly disjoint over `F`,
  if they are linearly disjoint as subalgebras (`Subalgebra.LinearDisjoint`).

## Implementation notes

The `Subalgebra.LinearDisjoint` is stated for two `Subalgebra`s. The original design of
`IntermediateField.LinearDisjoint` is also stated for two `IntermediateField`s
(see `IntermediateField.linearDisjoint_iff'` for the original statement).
But it's probably useful if one of them can be generalized to an abstract field
(see <https://github.com/leanprover-community/mathlib4/pull/9651#discussion_r1464070324>).
This leads to the current design of `IntermediateField.LinearDisjoint`
which is for one `IntermediateField` and one abstract field.
It is not generalized to two abstract fields as this will break the dot notation.

## Main results

### Equivalent characterization of linear disjointness

- `IntermediateField.LinearDisjoint.linearIndependent_left`:
  if `A` and `L` are linearly disjoint, then any `F`-linearly independent family on `A` remains
  linearly independent over `L`.

- `IntermediateField.LinearDisjoint.of_basis_left`:
  conversely, if there exists an `F`-basis of `A` which remains linearly independent over `L`, then
  `A` and `L` are linearly disjoint.

- `IntermediateField.LinearDisjoint.linearIndependent_right`:
  `IntermediateField.LinearDisjoint.linearIndependent_right'`:
  if `A` and `L` are linearly disjoint, then any `F`-linearly independent family on `L` remains
  linearly independent over `A`.

- `IntermediateField.LinearDisjoint.of_basis_right`:
  `IntermediateField.LinearDisjoint.of_basis_right'`:
  conversely, if there exists an `F`-basis of `L` which remains linearly independent over `A`, then
  `A` and `L` are linearly disjoint.

- `IntermediateField.LinearDisjoint.linearIndependent_mul`:
  `IntermediateField.LinearDisjoint.linearIndependent_mul'`:
  if `A` and `L` are linearly disjoint, then for any family of
  `F`-linearly independent elements `{ a_i }` of `A`, and any family of
  `F`-linearly independent elements `{ b_j }` of `L`, the family `{ a_i * b_j }` in `S` is
  also `F`-linearly independent.

- `IntermediateField.LinearDisjoint.of_basis_mul`:
  `IntermediateField.LinearDisjoint.of_basis_mul'`:
  conversely, if `{ a_i }` is an `F`-basis of `A`, if `{ b_j }` is an `F`-basis of `L`,
  such that the family `{ a_i * b_j }` in `E` is `F`-linearly independent,
  then `A` and `L` are linearly disjoint.

### Equivalent characterization by `IsDomain` or `IsField` of tensor product

The following results are related to the equivalent characterizations in
<https://mathoverflow.net/questions/8324>.

- `IntermediateField.LinearDisjoint.isDomain'`,
  `IntermediateField.LinearDisjoint.exists_field_of_isDomain`:
  if `A` and `B` are field extensions of `F`, then `A ⊗[F] B`
  is a domain if and only if there exists a field extension of `F` that `A` and `B`
  embed into with linearly disjoint images.

- `IntermediateField.LinearDisjoint.isField_of_forall`,
  `IntermediateField.LinearDisjoint.of_isField'`:
  if `A` and `B` are field extensions of `F`, then `A ⊗[F] B`
  is a field if and only if for any field extension of `F` that `A` and `B` embed into, their
  images are linearly disjoint.

- `Algebra.TensorProduct.isField_of_isAlgebraic`:
  if `E` and `K` are field extensions of `F`, one of them is algebraic, and
  `E ⊗[F] K` is a domain, then `E ⊗[F] K` is also a field.
  See `Algebra.TensorProduct.isAlgebraic_of_isField` for its converse (in an earlier file).

- `IntermediateField.LinearDisjoint.isField_of_isAlgebraic`,
  `IntermediateField.LinearDisjoint.isField_of_isAlgebraic'`:
  if `A` and `B` are field extensions of `F`, one of them is algebraic, such that they are linearly
  disjoint (more generally, if there exists a field extension of `F` that they embed into with
  linearly disjoint images), then `A ⊗[F] B` is a field.

### Other main results

- `IntermediateField.LinearDisjoint.symm`, `IntermediateField.linearDisjoint_comm`:
  linear disjointness is symmetric.

- `IntermediateField.LinearDisjoint.map`:
  linear disjointness is preserved by algebra homomorphism.

- `IntermediateField.LinearDisjoint.rank_sup`,
  `IntermediateField.LinearDisjoint.finrank_sup`:
  if `A` and `B` are linearly disjoint,
  then the rank of `A ⊔ B` is equal to the product of the rank of `A` and `B`.

- `IntermediateField.LinearDisjoint.of_finrank_sup`:
  conversely, if `A` and `B` are finite extensions,
  such that rank of `A ⊔ B` is equal to the product of the rank of `A` and `B`,
  then `A` and `B` are linearly disjoint.

- `IntermediateField.LinearDisjoint.of_finrank_coprime`:
  if the rank of `A` and `B` are coprime,
  then `A` and `B` are linearly disjoint.

- `IntermediateField.LinearDisjoint.inf_eq_bot`:
  if `A` and `B` are linearly disjoint, then they are disjoint.

- `IntermediateField.LinearDisjoint.algEquiv_of_isAlgebraic`:
  linear disjointness is preserved by isomorphisms, provided that one of the field is algebraic.

## Tags

linearly disjoint, linearly independent, tensor product

-/

open scoped TensorProduct

open Module IntermediateField

noncomputable section

universe u v w

namespace IntermediateField

variable {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]

variable (A B : IntermediateField F E)

variable (L : Type w) [Field L] [Algebra F L] [Algebra L E] [IsScalarTower F L E]

protected abbrev LinearDisjoint : Prop :=
  A.toSubalgebra.LinearDisjoint (IsScalarTower.toAlgHom F L E).range

variable {A B L}

theorem linearDisjoint_iff' :
    A.LinearDisjoint B ↔ A.toSubalgebra.LinearDisjoint B.toSubalgebra := by
  rw [linearDisjoint_iff]
  congr!
  ext; simp

theorem LinearDisjoint.symm (H : A.LinearDisjoint B) : B.LinearDisjoint A :=
  linearDisjoint_iff'.2 (linearDisjoint_iff'.1 H).symm

theorem linearDisjoint_comm : A.LinearDisjoint B ↔ B.LinearDisjoint A :=
  ⟨LinearDisjoint.symm, LinearDisjoint.symm⟩

variable {L' : Type*} [Field L'] [Algebra F L'] [Algebra L' E] [IsScalarTower F L' E]

theorem LinearDisjoint.symm' (H : (IsScalarTower.toAlgHom F L E).fieldRange.LinearDisjoint L') :
    (IsScalarTower.toAlgHom F L' E).fieldRange.LinearDisjoint L :=
  Subalgebra.LinearDisjoint.symm H

theorem linearDisjoint_comm' :
    (IsScalarTower.toAlgHom F L E).fieldRange.LinearDisjoint L' ↔
    (IsScalarTower.toAlgHom F L' E).fieldRange.LinearDisjoint L :=
  ⟨LinearDisjoint.symm', LinearDisjoint.symm'⟩

end

namespace LinearDisjoint

theorem map (H : A.LinearDisjoint B) {K : Type*} [Field K] [Algebra F K]
    (f : E →ₐ[F] K) : (A.map f).LinearDisjoint (B.map f) :=
  linearDisjoint_iff'.2 ((linearDisjoint_iff'.1 H).map f f.injective)

theorem map' (H : A.LinearDisjoint L) (K : Type*) [Field K] [Algebra F K] [Algebra L K]
    [IsScalarTower F L K] [Algebra E K] [IsScalarTower F E K] [IsScalarTower L E K] :
    (A.map (IsScalarTower.toAlgHom F E K)).LinearDisjoint L := by
  rw [linearDisjoint_iff] at H ⊢
  have := H.map (IsScalarTower.toAlgHom F E K) (RingHom.injective _)
  rw [← AlgHom.range_comp] at this
  convert this
  ext; exact IsScalarTower.algebraMap_apply L E K _

theorem map'' {L' : Type*} [Field L'] [Algebra F L'] [Algebra L' E] [IsScalarTower F L' E]
    (H : (IsScalarTower.toAlgHom F L E).fieldRange.LinearDisjoint L')
    (K : Type*) [Field K] [Algebra F K] [Algebra L K] [IsScalarTower F L K]
    [Algebra L' K] [IsScalarTower F L' K] [Algebra E K] [IsScalarTower F E K]
    [IsScalarTower L E K] [IsScalarTower L' E K] :
    (IsScalarTower.toAlgHom F L K).fieldRange.LinearDisjoint L' := by
  rw [linearDisjoint_iff] at H ⊢
  have := H.map (IsScalarTower.toAlgHom F E K) (RingHom.injective _)
  simp_rw [AlgHom.fieldRange_toSubalgebra, ← AlgHom.range_comp] at this
  rw [AlgHom.fieldRange_toSubalgebra]
  convert this <;> (ext; exact IsScalarTower.algebraMap_apply _ E K _)

variable (A) in

theorem self_right : A.LinearDisjoint F := Subalgebra.LinearDisjoint.bot_right _

variable (A) in

theorem bot_right : A.LinearDisjoint (⊥ : IntermediateField F E) :=
  linearDisjoint_iff'.2 (Subalgebra.LinearDisjoint.bot_right _)

variable (F E L) in

theorem bot_left : (⊥ : IntermediateField F E).LinearDisjoint L :=
  Subalgebra.LinearDisjoint.bot_left _

theorem linearIndependent_left (H : A.LinearDisjoint L)
    {ι : Type*} {a : ι → A} (ha : LinearIndependent F a) : LinearIndependent L (A.val ∘ a) :=
  (Subalgebra.LinearDisjoint.linearIndependent_left_of_flat H ha).map_of_injective_injective
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)) (AddMonoidHom.id E)
    (by simp) (by simp) (fun _ _ ↦ by simp_rw [Algebra.smul_def]; rfl)

theorem of_basis_left {ι : Type*} (a : Basis ι F A)
    (H : LinearIndependent L (A.val ∘ a)) : A.LinearDisjoint L :=
  Subalgebra.LinearDisjoint.of_basis_left _ _ a <| H.map_of_surjective_injective
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)) (AddMonoidHom.id E)
    (AlgEquiv.surjective _) (by simp) (fun _ _ ↦ by simp_rw [Algebra.smul_def]; rfl)

theorem linearIndependent_right (H : A.LinearDisjoint B)
    {ι : Type*} {b : ι → B} (hb : LinearIndependent F b) : LinearIndependent A (B.val ∘ b) :=
  (linearDisjoint_iff'.1 H).linearIndependent_right_of_flat hb

noncomputable def basisOfBasisRight (H : A.LinearDisjoint B)
    (H' : A.toSubalgebra ⊔ B.toSubalgebra = ⊤) {ι : Type*} (b : Basis ι F B) :
    Basis ι A E :=
  (linearDisjoint_iff'.mp H).basisOfBasisRight H' b
