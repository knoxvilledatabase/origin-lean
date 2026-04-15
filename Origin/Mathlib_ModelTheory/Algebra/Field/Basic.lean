/-
Extracted from ModelTheory/Algebra/Field/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The First-Order Theory of Fields

This file defines the first-order theory of fields as a theory over the language of rings.

## Main definitions

- `FirstOrder.Language.Theory.field` : the theory of fields
- `FirstOrder.Model.fieldOfModelField` : a model of the theory of fields on a type `K` that
  already has ring operations.
- `FirstOrder.Model.compatibleRingOfModelField` : shows that the ring operations on `K` given
  by `fieldOfModelField` are compatible with the ring operations on `K` given by the
  `Language.ring.Structure` instance.
-/

variable {K : Type*}

namespace FirstOrder

namespace Field

open Language Ring Structure BoundedFormula

inductive FieldAxiom : Type
  | addAssoc : FieldAxiom
  | zeroAdd : FieldAxiom
  | negAddCancel : FieldAxiom
  | mulAssoc : FieldAxiom
  | mulComm : FieldAxiom
  | oneMul : FieldAxiom
  | existsInv : FieldAxiom
  | leftDistrib : FieldAxiom
  | existsPairNE : FieldAxiom
