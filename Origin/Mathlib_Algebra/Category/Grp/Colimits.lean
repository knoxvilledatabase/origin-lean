/-
Extracted from Algebra/Category/Grp/Colimits.lean
Genuine: 5 of 6 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The category of additive commutative groups has all colimits.

This file constructs colimits in the category of additive commutative groups, as
quotients of finitely supported functions.

-/

universe u' w u v

open CategoryTheory Limits

namespace AddCommGrpCat

variable {J : Type u} [Category.{v} J] (F : J ⥤ AddCommGrpCat.{w})

namespace Colimits

/-!
We build the colimit of a diagram in `AddCommGrpCat` by constructing the
free group on the disjoint union of all the abelian groups in the diagram,
then taking the quotient by the abelian group laws within each abelian group,
and the identifications given by the morphisms in the diagram.
-/

abbrev Relations [DecidableEq J] : AddSubgroup (DFinsupp (fun j ↦ F.obj j)) :=
  AddSubgroup.closure {x | ∃ (j j' : J) (u : j ⟶ j') (a : F.obj j),
    x = DFinsupp.single j' (F.map u a) - DFinsupp.single j a}

def Quot [DecidableEq J] : Type (max u w) :=
  DFinsupp (fun j ↦ F.obj j) ⧸ Relations F

-- INSTANCE (free from Core): [DecidableEq

def Quot.ι [DecidableEq J] (j : J) : F.obj j →+ Quot F :=
  (QuotientAddGroup.mk' _).comp (DFinsupp.singleAddHom (fun j ↦ F.obj j) j)

lemma Quot.addMonoidHom_ext [DecidableEq J] {α : Type*} [AddMonoid α] {f g : Quot F →+ α}
    (h : ∀ (j : J) (x : F.obj j), f (Quot.ι F j x) = g (Quot.ι F j x)) : f = g :=
  QuotientAddGroup.addMonoidHom_ext _ (DFinsupp.addHom_ext h)

variable (c : Cocone F)

set_option backward.isDefEq.respectTransparency false in

def Quot.desc [DecidableEq J] : Quot.{w} F →+ c.pt := by
  refine QuotientAddGroup.lift _ (DFinsupp.sumAddHom fun x => (c.ι.app x).hom) ?_
  dsimp
  rw [AddSubgroup.closure_le]
  intro _ ⟨_, _, _, _, eq⟩
  rw [eq]
  simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, DFinsupp.sumAddHom_single]
  change (F.map _ ≫ c.ι.app _) _ - _ = 0
  rw [c.ι.naturality]
  simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id, sub_self]

set_option backward.isDefEq.respectTransparency false in
