/-
Extracted from Algebra/Homology/Embedding/StupidTrunc.lean
Genuine: 5 of 7 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# The stupid truncation of homological complexes

Given an embedding `e : c.Embedding c'` of complex shapes, we define
a functor `stupidTruncFunctor : HomologicalComplex C c' ⥤ HomologicalComplex C c'`
which sends `K` to `K.stupidTrunc e` which is defined as `(K.restriction e).extend e`.

## TODO (@joelriou)
* define the inclusion `e.stupidTruncFunctor C ⟶ 𝟭 _` when `[e.IsTruncGE]`;
* define the projection `𝟭 _ ⟶ e.stupidTruncFunctor C` when `[e.IsTruncLE]`.

-/

open CategoryTheory Category Limits ZeroObject

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

namespace HomologicalComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

variable (K L M : HomologicalComplex C c') (φ : K ⟶ L) (φ' : L ⟶ M)
  (e : c.Embedding c') [e.IsRelIff]

noncomputable def stupidTrunc : HomologicalComplex C c' := ((K.restriction e).extend e)

-- INSTANCE (free from Core): :

noncomputable def stupidTruncXIso {i : ι} {i' : ι'} (hi' : e.f i = i') :
    (K.stupidTrunc e).X i' ≅ K.X i' :=
  (K.restriction e).extendXIso e hi' ≪≫ eqToIso (by subst hi'; rfl)

lemma isZero_stupidTrunc_X (i' : ι') (hi' : ∀ i, e.f i ≠ i') :
    IsZero ((K.stupidTrunc e).X i') :=
  isZero_extend_X _ _ _ hi'

-- INSTANCE (free from Core): {ι''

lemma isZero_stupidTrunc_iff :
    IsZero (K.stupidTrunc e) ↔ K.IsStrictlySupportedOutside e := by
  constructor
  · exact fun h ↦ ⟨fun i ↦
      ((eval _ _ (e.f i)).map_isZero h).of_iso (K.stupidTruncXIso e rfl).symm⟩
  · intro h
    rw [isZero_iff_isStrictlySupported_and_isStrictlySupportedOutside _ e]
    constructor
    · infer_instance
    · exact ⟨fun i ↦ (h.isZero i).of_iso (K.stupidTruncXIso e rfl)⟩

variable {K L M}

noncomputable def stupidTruncMap : K.stupidTrunc e ⟶ L.stupidTrunc e :=
  extendMap (restrictionMap φ e) e

variable (K) in
