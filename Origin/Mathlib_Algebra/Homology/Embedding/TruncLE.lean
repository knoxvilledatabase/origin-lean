/-
Extracted from Algebra/Homology/Embedding/TruncLE.lean
Genuine: 12 of 12 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The canonical truncation

Given an embedding `e : Embedding c c'` of complex shapes which
satisfies `e.IsTruncLE` and `K : HomologicalComplex C c'`,
we define `K.truncGE' e : HomologicalComplex C c`
and `K.truncLE e : HomologicalComplex C c'` which are the canonical
truncations of `K` relative to `e`.

In order to achieve this, we dualize the constructions from the file
`Embedding.TruncGE`.

-/

open CategoryTheory Limits ZeroObject Category

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]

namespace HomologicalComplex

variable (K L M : HomologicalComplex C c') (φ : K ⟶ L) (φ' : L ⟶ M)
  (e : c.Embedding c') [e.IsTruncLE]
  [∀ i', K.HasHomology i'] [∀ i', L.HasHomology i'] [∀ i', M.HasHomology i']

noncomputable def truncLE' : HomologicalComplex C c := (K.op.truncGE' e.op).unop

noncomputable def truncLE'XIso {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : ¬ e.BoundaryLE i) :
    (K.truncLE' e).X i ≅ K.X i' :=
  (K.op.truncGE'XIso e.op hi' (by simpa)).symm.unop

noncomputable def truncLE'XIsoCycles {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : e.BoundaryLE i) :
    (K.truncLE' e).X i ≅ K.cycles i' :=
  (K.op.truncGE'XIsoOpcycles e.op hi' (by simpa)).unop.symm ≪≫
    (K.opcyclesOpIso i').unop.symm

lemma truncLE'_d_eq {i j : ι} (hij : c.Rel i j) {i' j' : ι'}
    (hi' : e.f i = i') (hj' : e.f j = j') (hj : ¬ e.BoundaryLE j) :
    (K.truncLE' e).d i j = (K.truncLE'XIso e hi' (e.not_boundaryLE_prev hij)).hom ≫ K.d i' j' ≫
        (K.truncLE'XIso e hj' hj).inv :=
  Quiver.Hom.op_inj (by simpa using K.op.truncGE'_d_eq e.op hij hj' hi' (by simpa))

lemma truncLE'_d_eq_toCycles {i j : ι} (hij : c.Rel i j) {i' j' : ι'}
    (hi' : e.f i = i') (hj' : e.f j = j') (hj : e.BoundaryLE j) :
    (K.truncLE' e).d i j = (K.truncLE'XIso e hi' (e.not_boundaryLE_prev hij)).hom ≫
      K.toCycles i' j' ≫ (K.truncLE'XIsoCycles e hj' hj).inv :=
  Quiver.Hom.op_inj (by
    simpa [truncLE', truncLE'XIso, truncLE'XIsoCycles]
      using K.op.truncGE'_d_eq_fromOpcycles e.op hij hj' hi' (by simpa))

variable [HasZeroObject C]

noncomputable def truncLE : HomologicalComplex C c' := (K.op.truncGE e.op).unop

noncomputable def truncLEIso : K.truncLE e ≅ (K.truncLE' e).extend e :=
  (unopFunctor C c'.symm).mapIso ((K.truncLE' e).extendOpIso e).symm.op

noncomputable def truncLEXIso {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : ¬ e.BoundaryLE i) :
    (K.truncLE e).X i' ≅ K.X i' :=
  (K.op.truncGEXIso e.op hi' (by simpa)).unop.symm

noncomputable def truncLEXIsoCycles {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : e.BoundaryLE i) :
    (K.truncLE e).X i' ≅ K.cycles i' :=
  (K.op.truncGEXIsoOpcycles e.op hi' (by simpa)).unop.symm ≪≫
    (K.opcyclesOpIso i').unop.symm

end

variable {K L M}

noncomputable def truncLE'Map : K.truncLE' e ⟶ L.truncLE' e :=
  (unopFunctor C c.symm).map (truncGE'Map ((opFunctor C c').map φ.op) e.op).op

set_option backward.isDefEq.respectTransparency false in

lemma truncLE'Map_f_eq_cyclesMap {i : ι} (hi : e.BoundaryLE i) {i' : ι'} (h : e.f i = i') :
    (truncLE'Map φ e).f i =
      (K.truncLE'XIsoCycles e h hi).hom ≫ cyclesMap φ i' ≫
        (L.truncLE'XIsoCycles e h hi).inv := by
  apply Quiver.Hom.op_inj
  dsimp [truncLE'Map, truncLE'XIsoCycles]
  rw [assoc, assoc, truncGE'Map_f_eq_opcyclesMap _ e.op (by simpa) h,
    opcyclesOpIso_inv_naturality_assoc, Iso.hom_inv_id_assoc]

lemma truncLE'Map_f_eq {i : ι} (hi : ¬ e.BoundaryLE i) {i' : ι'} (h : e.f i = i') :
    (truncLE'Map φ e).f i =
      (K.truncLE'XIso e h hi).hom ≫ φ.f i' ≫ (L.truncLE'XIso e h hi).inv :=
  Quiver.Hom.op_inj
    (by simpa using truncGE'Map_f_eq ((opFunctor C c').map φ.op) e.op (by simpa) h)

variable (K) in
