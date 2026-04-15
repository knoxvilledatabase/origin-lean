/-
Extracted from CategoryTheory/Presentable/CardinalFilteredPresentation.lean
Genuine: 8 of 14 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core

/-!
# Presentable generators

Let `C` be a category, a regular cardinal `κ` and `P : ObjectProperty C`.
We define a predicate `P.IsCardinalFilteredGenerator κ` saying that
`P` consists of `κ`-presentable objects and that any object in `C`
is a `κ`-filtered colimit of objects satisfying `P`.
We show that if this condition is satisfied, then `P` is a strong generator
(see `IsCardinalFilteredGenerator.isStrongGenerator`). Moreover,
if `C` is locally small, we show that any object in `C` is presentable
(see `IsCardinalFilteredGenerator.presentable`).

Finally, we define a typeclass `HasCardinalFilteredGenerator C κ` saying
that `C` is locally `w`-small and that there exists an (essentially) small `P`
such that `P.IsCardinalFilteredGenerator κ` holds.

## References
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace Limits.ColimitPresentation

lemma isCardinalPresentable {X : C} {J : Type w} [SmallCategory J]
    (p : ColimitPresentation J X) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    (h : ∀ (j : J), IsCardinalPresentable (p.diag.obj j) κ) [LocallySmall.{w} C]
    (κ' : Cardinal.{w}) [Fact κ'.IsRegular] (h : κ ≤ κ')
    (hJ : HasCardinalLT (Arrow J) κ') :
    IsCardinalPresentable X κ' :=
  have (k : J) : IsCardinalPresentable (p.diag.obj k) κ' := isCardinalPresentable_of_le _ h
  isCardinalPresentable_of_isColimit _ p.isColimit κ' hJ

end Limits.ColimitPresentation

open Limits

namespace ObjectProperty

variable {P : ObjectProperty C}

lemma ColimitOfShape.isCardinalPresentable {X : C} {J : Type w} [SmallCategory J]
    (p : P.ColimitOfShape J X) {κ : Cardinal.{w}} [Fact κ.IsRegular]
    (hP : P ≤ isCardinalPresentable C κ) [LocallySmall.{w} C]
    (κ' : Cardinal.{w}) [Fact κ'.IsRegular] (h : κ ≤ κ')
    (hJ : HasCardinalLT (Arrow J) κ') :
    IsCardinalPresentable X κ' :=
  p.toColimitPresentation.isCardinalPresentable κ
    (fun j ↦ hP _ (p.prop_diag_obj j)) _ h hJ

variable {κ : Cardinal.{w}} [Fact κ.IsRegular]

variable (P κ) in

structure IsCardinalFilteredGenerator : Prop where
  le_isCardinalPresentable : P ≤ isCardinalPresentable C κ
  exists_colimitsOfShape (X : C) :
    ∃ (J : Type w) (_ : SmallCategory J) (_ : IsCardinalFiltered J κ),
      P.colimitsOfShape J X

namespace IsCardinalFilteredGenerator

variable (h : P.IsCardinalFilteredGenerator κ) (X : C)

include h in

include h in

lemma isoClosure_iff :
    P.isoClosure.IsCardinalFilteredGenerator κ ↔ P.IsCardinalFilteredGenerator κ :=
  ⟨fun h ↦ h.of_le_isoClosure (by rfl) (P.le_isoClosure.trans h.le_isCardinalPresentable),
    isoClosure⟩

include h in

include h in

include h in

include h in

lemma essentiallySmall_isPresentable
    [ObjectProperty.EssentiallySmall.{w} P] [LocallySmall.{w} C] :
    ObjectProperty.EssentiallySmall.{w} (isCardinalPresentable C κ) := by
  rw [h.isPresentable_eq_retractClosure]
  infer_instance

end IsCardinalFilteredGenerator

end ObjectProperty

class HasCardinalFilteredGenerator (C : Type u) [hC : Category.{v} C]
    (κ : Cardinal.{w}) [hκ : Fact κ.IsRegular] : Prop extends LocallySmall.{w} C where
  exists_generator (C κ) [hC] [hκ] :
    ∃ (P : ObjectProperty C) (_ : ObjectProperty.EssentiallySmall.{w} P),
      P.IsCardinalFilteredGenerator κ

lemma ObjectProperty.IsCardinalFilteredGenerator.hasCardinalFilteredGenerator
    {P : ObjectProperty C} [ObjectProperty.EssentiallySmall.{w} P]
    [LocallySmall.{w} C] {κ : Cardinal.{w}} [hκ : Fact κ.IsRegular]
    (hP : P.IsCardinalFilteredGenerator κ) :
    HasCardinalFilteredGenerator C κ where
  exists_generator := ⟨P, inferInstance, hP⟩

lemma HasCardinalFilteredGenerator.exists_small_generator (C : Type u) [Category.{v} C]
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [HasCardinalFilteredGenerator C κ] :
    ∃ (P : ObjectProperty C) (_ : ObjectProperty.Small.{w} P),
      P.IsCardinalFilteredGenerator κ := by
  obtain ⟨P, _, hP⟩ := HasCardinalFilteredGenerator.exists_generator C κ
  obtain ⟨Q, _, h₁, h₂⟩ := ObjectProperty.EssentiallySmall.exists_small_le P
  exact ⟨Q, inferInstance, hP.of_le_isoClosure h₂ (h₁.trans hP.le_isCardinalPresentable)⟩

-- INSTANCE (free from Core): (C
