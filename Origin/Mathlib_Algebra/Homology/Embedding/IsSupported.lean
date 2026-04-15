/-
Extracted from Algebra/Homology/Embedding/IsSupported.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Support of homological complexes

Given an embedding `e : c.Embedding c'` of complex shapes, we say
that `K : HomologicalComplex C c'` is supported (resp. strictly supported) on `e`
if `K` is exact in degree `i'` (resp. `K.X i'` is zero) whenever `i'` is
not of the form `e.f i`. This defines two typeclasses `K.IsSupported e`
and `K.IsStrictlySupported e`.

We also define predicates `K.IsSupportedOutside e` and `K.IsStrictlySupportedOutside e`
when the conditions above are satisfied for those `i'` that are of the form `e.f i`.
(These two predicates are not made typeclasses because in most practical applications,
they are equivalent to `K.IsSupported e'` or `K.IsStrictlySupported e'` for a
complementary embedding `e'`.)

-/

open CategoryTheory Limits ZeroObject

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

namespace HomologicalComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (K L : HomologicalComplex C c') (e' : K ≅ L) (φ : K ⟶ L) (e : c.Embedding c')

class IsStrictlySupported : Prop where
  isZero (i' : ι') (hi' : ∀ i, e.f i ≠ i') : IsZero (K.X i')

lemma isZero_X_of_isStrictlySupported [K.IsStrictlySupported e]
    (i' : ι') (hi' : ∀ i, e.f i ≠ i') :
    IsZero (K.X i') :=
  IsStrictlySupported.isZero i' hi'

include e' in

variable {K L} in

lemma isStrictlySupported_of_iso [K.IsStrictlySupported e] : L.IsStrictlySupported e where
  isZero i' hi' := (K.isZero_X_of_isStrictlySupported e i' hi').of_iso
    ((eval _ _ i').mapIso e'.symm)
