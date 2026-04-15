/-
Extracted from FieldTheory/Fixed.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Fixed field under a group action.

This is the basis of the Fundamental Theorem of Galois Theory.
Given a (finite) group `G` that acts on a field `F`, we define `FixedPoints.subfield G F`,
the subfield consisting of elements of `F` fixed_points by every element of `G`.

This subfield is then normal and separable, and in addition if `G` acts faithfully on `F`
then `finrank (FixedPoints.subfield G F) F = Fintype.card G`.

## Main Definitions

- `FixedPoints.subfield G F`, the subfield consisting of elements of `F` fixed_points by every
element of `G`, where `G` is a group that acts on `F`.

-/

noncomputable section

open MulAction Finset Module

universe u v w

variable {M : Type u} [Monoid M]

variable (G : Type u) [Group G]

variable (K : Type*) (F : Type v) [Field F] [MulSemiringAction M F] [MulSemiringAction G F] (m : M)

def FixedBy.subfield : Subfield F where
  carrier := fixedBy F m
  zero_mem' := smul_zero m
  add_mem' hx hy := (smul_add m _ _).trans <| congr_arg₂ _ hx hy
  neg_mem' hx := (smul_neg m _).trans <| congr_arg _ hx
  one_mem' := smul_one m
  mul_mem' hx hy := (smul_mul' m _ _).trans <| congr_arg₂ _ hx hy
  inv_mem' x hx := (smul_inv'' m x).trans <| congr_arg _ hx
