/-
Extracted from Algebra/Homology/Embedding/TruncGE.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The canonical truncation

Given an embedding `e : Embedding c c'` of complex shapes which
satisfies `e.IsTruncGE` and `K : HomologicalComplex C c'`,
we define `K.truncGE' e : HomologicalComplex C c`
and `K.truncGE e : HomologicalComplex C c'` which are the canonical
truncations of `K` relative to `e`.

For example, if `e` is the embedding `embeddingUpIntGE p` of `ComplexShape.up ℕ`
in `ComplexShape.up ℤ` which sends `n : ℕ` to `p + n` and `K : CochainComplex C ℤ`,
then `K.truncGE' e : CochainComplex C ℕ` is the following complex:

`Q ⟶ K.X (p + 1) ⟶ K.X (p + 2) ⟶ K.X (p + 3) ⟶ ...`

where in degree `0`, the object `Q` identifies to the cokernel
of `K.X (p - 1) ⟶ K.X p` (this is `K.opcycles p`). Then, the
cochain complex `K.truncGE e` is indexed by `ℤ`, and has the
following shape:

`... ⟶ 0 ⟶ 0 ⟶ 0 ⟶ Q ⟶ K.X (p + 1) ⟶ K.X (p + 2) ⟶ K.X (p + 3) ⟶ ...`

where `Q` is in degree `p`.

We also construct the canonical epimorphism `K.πTruncGE e : K ⟶ K.truncGE e`.

## TODO
* show that `K.πTruncGE e : K ⟶ K.truncGE e` induces an isomorphism
  in homology in degrees in the image of `e.f`.

-/

open CategoryTheory Limits ZeroObject Category

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]

namespace HomologicalComplex

variable (K L M : HomologicalComplex C c') (φ : K ⟶ L) (φ' : L ⟶ M)
  (e : c.Embedding c') [e.IsTruncGE]
  [∀ i', K.HasHomology i'] [∀ i', L.HasHomology i'] [∀ i', M.HasHomology i']

namespace truncGE'

open Classical in

noncomputable def X (i : ι) : C :=
  if e.BoundaryGE i
  then K.opcycles (e.f i)
  else K.X (e.f i)

noncomputable def XIsoOpcycles {i : ι} (hi : e.BoundaryGE i) :
    X K e i ≅ K.opcycles (e.f i) :=
  eqToIso (if_pos hi)

noncomputable def XIso {i : ι} (hi : ¬ e.BoundaryGE i) :
    X K e i ≅ K.X (e.f i) :=
  eqToIso (if_neg hi)

open Classical in

noncomputable def d (i j : ι) : X K e i ⟶ X K e j :=
  if hij : c.Rel i j
  then
    if hi : e.BoundaryGE i
    then (truncGE'.XIsoOpcycles K e hi).hom ≫ K.fromOpcycles (e.f i) (e.f j) ≫
      (XIso K e (e.not_boundaryGE_next hij)).inv
    else (XIso K e hi).hom ≫ K.d (e.f i) (e.f j) ≫
      (XIso K e (e.not_boundaryGE_next hij)).inv
  else 0
