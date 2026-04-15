/-
Extracted from Algebra/Category/ModuleCat/FilteredColimits.lean
Genuine: 9 of 11 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# The forgetful functor from `R`-modules preserves filtered colimits.

Forgetful functors from algebraic categories usually don't preserve colimits. However, they tend
to preserve _filtered_ colimits.

In this file, we start with a ring `R`, a small filtered category `J` and a functor
`F : J ⥤ ModuleCat R`. We show that the colimit of `F ⋙ forget₂ (ModuleCat R) AddCommGrpCat`
(in `AddCommGrpCat`) carries the structure of an `R`-module, thereby showing that the forgetful
functor `forget₂ (ModuleCat R) AddCommGrpCat` preserves filtered colimits. In particular, this
implies that `forget (ModuleCat R)` preserves filtered colimits.

-/

universe v u

noncomputable section

open CategoryTheory CategoryTheory.Limits ConcreteCategory

open CategoryTheory.IsFiltered renaming max → max' -- avoid name collision with `_root_.max`.

namespace ModuleCat.FilteredColimits

variable {R : Type u} [Ring R] {J : Type v} [SmallCategory J] [IsFiltered J]

variable (F : J ⥤ ModuleCat.{max v u, u} R)

def M : AddCommGrpCat :=
  AddCommGrpCat.FilteredColimits.colimit.{v, u}
    (F ⋙ forget₂ (ModuleCat R) AddCommGrpCat.{max v u})

def M.mk : (Σ j, F.obj j) → M F :=
  fun x ↦ (F ⋙ forget (ModuleCat R)).ιColimitType x.1 x.2

lemma M.mk_surjective (m : M F) :
    ∃ (j : J) (x : F.obj j), M.mk F ⟨j, x⟩ = m :=
  (F ⋙ forget (ModuleCat R)).ιColimitType_jointly_surjective m

theorem M.mk_eq (x y : Σ j, F.obj j)
    (h : ∃ (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k), F.map f x.2 = F.map g y.2) : M.mk F x = M.mk F y :=
  Quot.eqvGen_sound (Types.FilteredColimit.eqvGen_colimitTypeRel_of_rel
    (F ⋙ forget (ModuleCat R)) x y h)

lemma M.mk_map {j k : J} (f : j ⟶ k) (x : F.obj j) :
    M.mk F ⟨k, F.map f x⟩ = M.mk F ⟨j, x⟩ :=
  M.mk_eq _ _ _ ⟨k, 𝟙 _, f, by simp⟩

def colimitSMulAux (r : R) (x : Σ j, F.obj j) : M F :=
  M.mk F ⟨x.1, r • x.2⟩

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): colimitHasSMul

lemma colimit_zero_eq (j : J) :
    0 = M.mk F ⟨j, 0⟩ := by
  apply AddMonCat.FilteredColimits.colimit_zero_eq

lemma colimit_add_mk_eq (x y : Σ j, F.obj j) (k : J)
    (f : x.1 ⟶ k) (g : y.1 ⟶ k) :
    M.mk _ x + M.mk _ y = M.mk _ ⟨k, F.map f x.2 + F.map g y.2⟩ := by
  apply AddMonCat.FilteredColimits.colimit_add_mk_eq

lemma colimit_add_mk_eq' {j : J} (x y : F.obj j) :
    M.mk F ⟨j, x⟩ + M.mk F ⟨j, y⟩ = M.mk F ⟨j, x + y⟩ := by
  apply AddMonCat.FilteredColimits.colimit_add_mk_eq'
