/-
Extracted from CategoryTheory/Limits/Shapes/ZeroObjects.lean
Genuine: 22 of 25 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Zero objects

A category "has a zero object" if it has an object which is both initial and terminal. Having a
zero object provides zero morphisms, as the unique morphisms factoring through the zero object;
see `CategoryTheory.Limits.Shapes.ZeroMorphisms`.

## References

* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]
-/

noncomputable section

universe v u v' u'

open CategoryTheory

open CategoryTheory.Category

variable {C : Type u} [Category.{v} C]

variable {D : Type u'} [Category.{v'} D]

namespace CategoryTheory

namespace Limits

structure IsZero (X : C) : Prop where
  /-- there are unique morphisms to the object -/
  unique_to : ∀ Y, Nonempty (Unique (X ⟶ Y))
  /-- there are unique morphisms from the object -/
  unique_from : ∀ Y, Nonempty (Unique (Y ⟶ X))

namespace IsZero

variable {X Y : C}

protected def to_ (h : IsZero X) (Y : C) : X ⟶ Y :=
  @default _ <| (h.unique_to Y).some.toInhabited

theorem eq_to (h : IsZero X) (f : X ⟶ Y) : f = h.to_ Y :=
  @Unique.eq_default _ (id _) _

theorem to_eq (h : IsZero X) (f : X ⟶ Y) : h.to_ Y = f :=
  (h.eq_to f).symm

protected def from_ (h : IsZero X) (Y : C) : Y ⟶ X :=
  @default _ <| (h.unique_from Y).some.toInhabited

theorem eq_from (h : IsZero X) (f : Y ⟶ X) : f = h.from_ Y :=
  @Unique.eq_default _ (id _) _

theorem from_eq (h : IsZero X) (f : Y ⟶ X) : h.from_ Y = f :=
  (h.eq_from f).symm

theorem eq_of_src (hX : IsZero X) (f g : X ⟶ Y) : f = g :=
  (hX.eq_to f).trans (hX.eq_to g).symm

theorem eq_of_tgt (hX : IsZero X) (f g : Y ⟶ X) : f = g :=
  (hX.eq_from f).trans (hX.eq_from g).symm

def iso (hX : IsZero X) (hY : IsZero Y) : X ≅ Y where
  hom := hX.to_ Y
  inv := hX.from_ Y
  hom_inv_id := hX.eq_of_src _ _
  inv_hom_id := hY.eq_of_src _ _

lemma isIso (hX : IsZero X) (hY : IsZero Y) (f : X ⟶ Y) : IsIso f :=
  ⟨hY.to_ _, hX.eq_of_src _ _, hY.eq_of_src _ _⟩

protected def isInitial (hX : IsZero X) : IsInitial X :=
  @IsInitial.ofUnique _ _ X fun Y => (hX.unique_to Y).some

protected def isTerminal (hX : IsZero X) : IsTerminal X :=
  @IsTerminal.ofUnique _ _ X fun Y => (hX.unique_from Y).some

def isoIsInitial (hX : IsZero X) (hY : IsInitial Y) : X ≅ Y :=
  IsInitial.uniqueUpToIso hX.isInitial hY

def isoIsTerminal (hX : IsZero X) (hY : IsTerminal Y) : X ≅ Y :=
  IsTerminal.uniqueUpToIso hX.isTerminal hY

theorem of_iso (hY : IsZero Y) (e : X ≅ Y) : IsZero X := by
  refine ⟨fun Z => ⟨⟨⟨e.hom ≫ hY.to_ Z⟩, fun f => ?_⟩⟩,
    fun Z => ⟨⟨⟨hY.from_ Z ≫ e.inv⟩, fun f => ?_⟩⟩⟩
  · rw [← cancel_epi e.inv]
    apply hY.eq_of_src
  · rw [← cancel_mono e.hom]
    apply hY.eq_of_tgt

theorem op (h : IsZero X) : IsZero (Opposite.op X) :=
  ⟨fun Y => ⟨⟨⟨(h.from_ (Opposite.unop Y)).op⟩, fun _ => Quiver.Hom.unop_inj (h.eq_of_tgt _ _)⟩⟩,
    fun Y => ⟨⟨⟨(h.to_ (Opposite.unop Y)).op⟩, fun _ => Quiver.Hom.unop_inj (h.eq_of_src _ _)⟩⟩⟩

theorem unop {X : Cᵒᵖ} (h : IsZero X) : IsZero (Opposite.unop X) :=
  ⟨fun Y => ⟨⟨⟨(h.from_ (Opposite.op Y)).unop⟩, fun _ => Quiver.Hom.op_inj (h.eq_of_tgt _ _)⟩⟩,
    fun Y => ⟨⟨⟨(h.to_ (Opposite.op Y)).unop⟩, fun _ => Quiver.Hom.op_inj (h.eq_of_src _ _)⟩⟩⟩

variable (Y) in

def retract (h : IsZero X) : Retract X Y where
  i := h.to_ Y
  r := h.from_ Y
  retract := h.isInitial.hom_ext _ _

end IsZero

end Limits

open CategoryTheory.Limits

theorem Iso.isZero_iff {X Y : C} (e : X ≅ Y) : IsZero X ↔ IsZero Y :=
  ⟨fun h => h.of_iso e.symm, fun h => h.of_iso e⟩

theorem Functor.isZero (F : C ⥤ D) (hF : ∀ X, IsZero (F.obj X)) : IsZero F := by
  constructor <;> intro G <;> refine ⟨⟨⟨?_⟩, ?_⟩⟩
  · refine
      { app := fun X => (hF _).to_ _
        naturality := ?_ }
    intros
    exact (hF _).eq_of_src _ _
  · intro f
    ext
    apply (hF _).eq_of_src _ _
  · refine
      { app := fun X => (hF _).from_ _
        naturality := ?_ }
    intros
    exact (hF _).eq_of_tgt _ _
  · intro f
    ext
    apply (hF _).eq_of_tgt _ _

namespace Limits

variable (C)

class HasZeroObject : Prop where
  /-- there exists a zero object -/
  zero : ∃ X : C, IsZero X

-- INSTANCE (free from Core): hasZeroObject_pUnit

variable [HasZeroObject C]
