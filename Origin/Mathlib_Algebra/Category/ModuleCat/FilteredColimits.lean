/-
Extracted from Algebra/Category/ModuleCat/FilteredColimits.lean
Genuine: 11 of 20 | Dissolved: 0 | Infrastructure: 9
-/
import Origin.Core
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# The forgetful functor from `R`-modules preserves filtered colimits.

Forgetful functors from algebraic categories usually don't preserve colimits. However, they tend
to preserve _filtered_ colimits.

In this file, we start with a ring `R`, a small filtered category `J` and a functor
`F : J ⥤ ModuleCat R`. We show that the colimit of `F ⋙ forget₂ (ModuleCat R) AddCommGrp`
(in `AddCommGrp`) carries the structure of an `R`-module, thereby showing that the forgetful
functor `forget₂ (ModuleCat R) AddCommGrp` preserves filtered colimits. In particular, this
implies that `forget (ModuleCat R)` preserves filtered colimits.

-/

universe v u

noncomputable section

open CategoryTheory CategoryTheory.Limits

open CategoryTheory.IsFiltered renaming max → max' -- avoid name collision with `_root_.max`.

open AddMonCat.FilteredColimits (colimit_zero_eq colimit_add_mk_eq)

namespace ModuleCat.FilteredColimits

section

variable {R : Type u} [Ring R] {J : Type v} [SmallCategory J] [IsFiltered J]

variable (F : J ⥤ ModuleCatMax.{v, u, u} R)

abbrev M : AddCommGrp :=
  AddCommGrp.FilteredColimits.colimit.{v, u}
    (F ⋙ forget₂ (ModuleCat R) AddCommGrp.{max v u})

abbrev M.mk : (Σ j, F.obj j) → M F :=
  Quot.mk (Types.Quot.Rel (F ⋙ forget (ModuleCat R)))

theorem M.mk_eq (x y : Σ j, F.obj j)
    (h : ∃ (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k), F.map f x.2 = F.map g y.2) : M.mk F x = M.mk F y :=
  Quot.eqvGen_sound (Types.FilteredColimit.eqvGen_quot_rel_of_rel (F ⋙ forget (ModuleCat R)) x y h)

def colimitSMulAux (r : R) (x : Σ j, F.obj j) : M F :=
  M.mk F ⟨x.1, r • x.2⟩

theorem colimitSMulAux_eq_of_rel (r : R) (x y : Σ j, F.obj j)
    (h : Types.FilteredColimit.Rel (F ⋙ forget (ModuleCat R)) x y) :
    colimitSMulAux F r x = colimitSMulAux F r y := by
  apply M.mk_eq
  obtain ⟨k, f, g, hfg⟩ := h
  use k, f, g
  simp only [Functor.comp_obj, Functor.comp_map, forget_map] at hfg
  simp [hfg]

instance colimitHasSMul : SMul R (M F) where
  smul r x := by
    refine Quot.lift (colimitSMulAux F r) ?_ x
    intro x y h
    apply colimitSMulAux_eq_of_rel
    apply Types.FilteredColimit.rel_of_quot_rel
    exact h

@[simp]
theorem colimit_smul_mk_eq (r : R) (x : Σ j, F.obj j) : r • M.mk F x = M.mk F ⟨x.1, r • x.2⟩ :=
  rfl

private theorem colimitModule.one_smul (x : (M F)) : (1 : R) • x = x := by
  refine Quot.inductionOn x ?_; clear x; intro x; obtain ⟨j, x⟩ := x
  erw [colimit_smul_mk_eq F 1 ⟨j, x⟩]
  simp
  rfl

instance colimitMulAction : MulAction R (M F) where
  one_smul x := by
    refine Quot.inductionOn x ?_; clear x; intro x; obtain ⟨j, x⟩ := x
    erw [colimit_smul_mk_eq F 1 ⟨j, x⟩, one_smul]
    rfl
  mul_smul r s x := by
    refine Quot.inductionOn x ?_; clear x; intro x; obtain ⟨j, x⟩ := x
    erw [colimit_smul_mk_eq F (r * s) ⟨j, x⟩, colimit_smul_mk_eq F s ⟨j, x⟩,
      colimit_smul_mk_eq F r ⟨j, _⟩, mul_smul]

instance colimitSMulWithZero : SMulWithZero R (M F) :=

{ colimitMulAction F with

  smul_zero := fun r => by

    erw [colimit_zero_eq _ (IsFiltered.nonempty.some : J), colimit_smul_mk_eq, smul_zero]

    rfl

  zero_smul := fun x => by

    refine Quot.inductionOn x ?_; clear x; intro x; obtain ⟨j, x⟩ := x

    erw [colimit_smul_mk_eq, zero_smul, colimit_zero_eq _ j]

    rfl }

private theorem colimitModule.add_smul (r s : R) (x : (M F)) : (r + s) • x = r • x + s • x := by
  refine Quot.inductionOn x ?_; clear x; intro x; obtain ⟨j, x⟩ := x
  erw [colimit_smul_mk_eq, _root_.add_smul, colimit_smul_mk_eq, colimit_smul_mk_eq,
      colimit_add_mk_eq _ ⟨j, _⟩ ⟨j, _⟩ j (𝟙 j) (𝟙 j)]
  simp only [Functor.comp_obj, forget₂_obj, Functor.comp_map, CategoryTheory.Functor.map_id,
    forget₂_map]
  rfl

instance colimitModule : Module R (M F) :=

{ colimitMulAction F,

  colimitSMulWithZero F with

  smul_add := fun r x y => by

    refine Quot.induction_on₂ x y ?_; clear x y; intro x y; obtain ⟨i, x⟩ := x; obtain ⟨j, y⟩ := y

    erw [colimit_add_mk_eq _ ⟨i, _⟩ ⟨j, _⟩ (max' i j) (IsFiltered.leftToMax i j)

      (IsFiltered.rightToMax i j), colimit_smul_mk_eq, smul_add, colimit_smul_mk_eq,

      colimit_smul_mk_eq, colimit_add_mk_eq _ ⟨i, _⟩ ⟨j, _⟩ (max' i j) (IsFiltered.leftToMax i j)

      (IsFiltered.rightToMax i j), LinearMap.map_smul, LinearMap.map_smul]

    rfl

  add_smul := colimitModule.add_smul F }

def colimit : ModuleCatMax.{v, u, u} R :=
  ModuleCat.of R (M F)

def coconeMorphism (j : J) : F.obj j ⟶ colimit F :=
  { (AddCommGrp.FilteredColimits.colimitCocone
      (F ⋙ forget₂ (ModuleCat R) AddCommGrp.{max v u})).ι.app j with
    map_smul' := fun r x => by erw [colimit_smul_mk_eq F r ⟨j, x⟩]; rfl }

def colimitCocone : Cocone F where
  pt := colimit F
  ι :=
    { app := coconeMorphism F
      naturality := fun _ _' f =>
        LinearMap.coe_injective
          ((Types.TypeMax.colimitCocone (F ⋙ forget (ModuleCat R))).ι.naturality f) }

def colimitDesc (t : Cocone F) : colimit F ⟶ t.pt :=
  { (AddCommGrp.FilteredColimits.colimitCoconeIsColimit
          (F ⋙ forget₂ (ModuleCatMax.{v, u} R) AddCommGrp.{max v u})).desc
      ((forget₂ (ModuleCat R) AddCommGrp.{max v u}).mapCocone t) with
    map_smul' := fun r x => by
      refine Quot.inductionOn x ?_; clear x; intro x; obtain ⟨j, x⟩ := x
      erw [colimit_smul_mk_eq]
      exact LinearMap.map_smul (t.ι.app j) r x }

def colimitCoconeIsColimit : IsColimit (colimitCocone F) where
  desc := colimitDesc F
  fac t j :=
    LinearMap.coe_injective <|
      (Types.TypeMax.colimitCoconeIsColimit.{v, u} (F ⋙ forget (ModuleCat R))).fac
        ((forget (ModuleCat R)).mapCocone t) j
  uniq t _ h :=
    LinearMap.coe_injective <|
      (Types.TypeMax.colimitCoconeIsColimit (F ⋙ forget (ModuleCat R))).uniq
        ((forget (ModuleCat R)).mapCocone t) _ fun j => funext fun x => LinearMap.congr_fun (h j) x

instance forget₂AddCommGroup_preservesFilteredColimits :
    PreservesFilteredColimits (forget₂ (ModuleCat.{u} R) AddCommGrp.{u}) where
  preserves_filtered_colimits J _ _ :=
  { -- Porting note: without the curly braces for `F`
    -- here we get a confusing error message about universes.
    preservesColimit := fun {F : J ⥤ ModuleCat.{u} R} =>
      preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit F)
        (AddCommGrp.FilteredColimits.colimitCoconeIsColimit
          (F ⋙ forget₂ (ModuleCat.{u} R) AddCommGrp.{u})) }

instance forget_preservesFilteredColimits : PreservesFilteredColimits (forget (ModuleCat.{u} R)) :=
  Limits.comp_preservesFilteredColimits (forget₂ (ModuleCat R) AddCommGrp)
    (forget AddCommGrp)

instance forget_reflectsFilteredColimits : ReflectsFilteredColimits (forget (ModuleCat.{u} R)) where
  reflects_filtered_colimits _ := { reflectsColimit := reflectsColimit_of_reflectsIsomorphisms _ _ }

end

end ModuleCat.FilteredColimits
