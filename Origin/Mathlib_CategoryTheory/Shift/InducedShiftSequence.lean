/-
Extracted from CategoryTheory/Shift/InducedShiftSequence.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Induced shift sequences

When `G : C ⥤ A` is a functor from a category equipped with a shift by a
monoid `M`, we have defined in the file `Mathlib/CategoryTheory/Shift/ShiftSequence.lean`
a type class `G.ShiftSequence M` which provides functors `G.shift a : C ⥤ A` for all `a : M`,
isomorphisms `shiftFunctor C n ⋙ G.shift a ≅ G.shift a'` when `n + a = a'`,
and isomorphisms `G.isoShift a : shiftFunctor C a ⋙ G ≅ G.shift a` for all `a`, all of
which satisfy good coherence properties. The idea is that it allows to use functors
`G.shift a` which may have better definitional properties than `shiftFunctor C a ⋙ G`.
The typical example shall be `[(homologyFunctor C (ComplexShape.up ℤ) 0).ShiftSequence ℤ]`
for any abelian category `C` (TODO).

Similarly as a shift on a category may induce a shift on a quotient or a localized
category (see the file `Mathlib/CategoryTheory/Shift/Induced.lean`), this file shows that
under certain assumptions, there is an induced "shift sequence". The main application
will be the construction of a shift sequence for the homology functor on the
homotopy category of cochain complexes (TODO), and also on the derived category (TODO).

-/

open CategoryTheory Category Functor

namespace CategoryTheory

variable {C D A : Type*} [Category* C] [Category* D] [Category* A]
  {L : C ⥤ D} {F : D ⥤ A} {G : C ⥤ A} (e : L ⋙ F ≅ G) (M : Type*)
  [AddMonoid M] [HasShift C M]
  [G.ShiftSequence M] (F' : M → D ⥤ A) (e' : ∀ m, L ⋙ F' m ≅ G.shift m)
  [((whiskeringLeft C D A).obj L).Full] [((whiskeringLeft C D A).obj L).Faithful]

namespace Functor

namespace ShiftSequence

namespace induced

noncomputable def isoZero : F' 0 ≅ F :=
  ((whiskeringLeft C D A).obj L).preimageIso (e' 0 ≪≫ G.isoShiftZero M ≪≫ e.symm)

lemma isoZero_hom_app_obj (X : C) :
    (isoZero e M F' e').hom.app (L.obj X) =
      (e' 0).hom.app X ≫ (isoShiftZero G M).hom.app X ≫ e.inv.app X :=
  NatTrans.congr_app (((whiskeringLeft C D A).obj L).map_preimage _) X

variable (L G)

variable [HasShift D M] [L.CommShift M]

noncomputable def shiftIso (n a a' : M) (ha' : n + a = a') :
    shiftFunctor D n ⋙ F' a ≅ F' a' := by
  exact ((whiskeringLeft C D A).obj L).preimageIso ((Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (L.commShiftIso n).symm _ ≪≫
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (e' a) ≪≫
    G.shiftIso n a a' ha' ≪≫ (e' a').symm)

lemma shiftIso_hom_app_obj (n a a' : M) (ha' : n + a = a') (X : C) :
    (shiftIso L G M F' e' n a a' ha').hom.app (L.obj X) =
      (F' a).map ((L.commShiftIso n).inv.app X) ≫
        (e' a).hom.app (X⟦n⟧) ≫ (G.shiftIso n a a' ha').hom.app X ≫ (e' a').inv.app X :=
  (NatTrans.congr_app (((whiskeringLeft C D A).obj L).map_preimage _) X).trans (by simp)

attribute [irreducible] isoZero shiftIso

end induced

variable [HasShift D M] [L.CommShift M]

set_option backward.isDefEq.respectTransparency false in
