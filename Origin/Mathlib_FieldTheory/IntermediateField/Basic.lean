/-
Extracted from FieldTheory/IntermediateField/Basic.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Intermediate fields

Let `L / K` be a field extension, given as an instance `Algebra K L`.
This file defines the type of fields in between `K` and `L`, `IntermediateField K L`.
An `IntermediateField K L` is a subfield of `L` which contains (the image of) `K`,
i.e. it is a `Subfield L` and a `Subalgebra K L`.

## Main definitions

* `IntermediateField K L` : the type of intermediate fields between `K` and `L`.
* `Subalgebra.to_intermediateField`: turns a subalgebra closed under `⁻¹`
  into an intermediate field
* `Subfield.to_intermediateField`: turns a subfield containing the image of `K`
  into an intermediate field
* `IntermediateField.map`: map an intermediate field along an `AlgHom`
* `IntermediateField.restrict_scalars`: restrict the scalars of an intermediate field to a smaller
  field in a tower of fields.

## Implementation notes

Intermediate fields are defined with a structure extending `Subfield` and `Subalgebra`.
A `Subalgebra` is closed under all operations except `⁻¹`,

## Tags
intermediate field, field extension
-/

open Polynomial

variable (K L L' : Type*) [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']

structure IntermediateField extends Subalgebra K L where
  inv_mem' : ∀ x ∈ carrier, x⁻¹ ∈ carrier

add_decl_doc IntermediateField.toSubalgebra

variable {K L L'}

variable (S : IntermediateField K L)

namespace IntermediateField

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

protected theorem neg_mem {x : L} (hx : x ∈ S) : -x ∈ S := by
  change -x ∈ S.toSubalgebra; simpa
