/-
Extracted from Algebra/Homology/Embedding/Extend.lean
Genuine: 8 of 8 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The extension of a homological complex by an embedding of complex shapes

Given an embedding `e : Embedding c c'` of complex shapes,
and `K : HomologicalComplex C c`, we define `K.extend e : HomologicalComplex C c'`, and this
leads to a functor `e.extendFunctor C : HomologicalComplex C c ⥤ HomologicalComplex C c'`.

This construction first appeared in the Liquid Tensor Experiment.

-/

open CategoryTheory Category Limits ZeroObject

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

namespace HomologicalComplex

variable {C : Type*} [Category* C] [HasZeroObject C]

variable [HasZeroMorphisms C] (K L M : HomologicalComplex C c)
  (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

namespace extend

noncomputable def X : Option ι → C
  | some x => K.X x
  | none => 0

noncomputable def XIso {i : Option ι} {j : ι} (hj : i = some j) :
    X K i ≅ K.X j := eqToIso (by subst hj; rfl)

lemma isZero_X {i : Option ι} (hi : i = none) :
    IsZero (X K i) := by
  subst hi
  exact Limits.isZero_zero _

noncomputable def XOpIso (i : Option ι) : X K.op i ≅ Opposite.op (X K i) :=
  match i with
  | some _ => Iso.refl _
  | none => IsZero.iso (isZero_X _ rfl) (isZero_X K rfl).op

noncomputable def d : ∀ (i j : Option ι), extend.X K i ⟶ extend.X K j
  | none, _ => 0
  | some i, some j => K.d i j
  | some _, none => 0

lemma d_none_eq_zero (i j : Option ι) (hi : i = none) :
    d K i j = 0 := by subst hi; rfl

lemma d_none_eq_zero' (i j : Option ι) (hj : j = none) :
    d K i j = 0 := by subst hj; cases i <;> rfl

lemma d_eq {i j : Option ι} {a b : ι} (hi : i = some a) (hj : j = some b) :
    d K i j = (XIso K hi).hom ≫ K.d a b ≫ (XIso K hj).inv := by
  subst hi hj
  simp [XIso, X, d]

set_option backward.isDefEq.respectTransparency false in
