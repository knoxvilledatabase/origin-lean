/-
Extracted from Algebra/Homology/Embedding/HomEquiv.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Relations between `extend` and `restriction`

Given an embedding `e : Embedding c c'` of complex shapes satisfying `e.IsRelIff`,
we obtain a bijection `e.homEquiv` between the type of morphisms
`K ⟶ L.extend e` (with `K : HomologicalComplex C c'` and `L : HomologicalComplex C c`)
and the subtype of morphisms `φ : K.restriction e ⟶ L` which satisfy a certain
condition `e.HasLift φ`.

## TODO
* obtain dual results for morphisms `L.extend e ⟶ K`.

-/

open CategoryTheory Category Limits

namespace ComplexShape

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : Embedding c c')
  {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

namespace Embedding

open HomologicalComplex

variable {K K' : HomologicalComplex C c'} {L L' : HomologicalComplex C c}
  [e.IsRelIff]

def HasLift (φ : K.restriction e ⟶ L) : Prop :=
  ∀ (j : ι) (_ : e.BoundaryGE j) (i' : ι')
    (_ : c'.Rel i' (e.f j)), K.d i' _ ≫ φ.f j = 0

namespace liftExtend

variable (φ : K.restriction e ⟶ L)

variable {e}

open Classical in

noncomputable def f (i' : ι') : K.X i' ⟶ (L.extend e).X i' :=
  if hi' : ∃ i, e.f i = i' then
    (K.restrictionXIso e hi'.choose_spec).inv ≫ φ.f hi'.choose ≫
      (L.extendXIso e hi'.choose_spec).inv
  else 0

lemma f_eq {i' : ι'} {i : ι} (hi : e.f i = i') :
    f φ i' = (K.restrictionXIso e hi).inv ≫ φ.f i ≫ (L.extendXIso e hi).inv := by
  have hi' : ∃ k, e.f k = i' := ⟨i, hi⟩
  have : hi'.choose = i := e.injective_f (by rw [hi'.choose_spec, hi])
  grind [f]

set_option backward.isDefEq.respectTransparency false in
