/-
Extracted from CategoryTheory/Functor/EpiMono.lean
Genuine: 25 of 37 | Dissolved: 0 | Infrastructure: 12
-/
import Origin.Core

/-!
# Preservation and reflection of monomorphisms and epimorphisms

We provide typeclasses that state that a functor preserves or reflects monomorphisms or
epimorphisms.
-/

open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {E : Type u₃}
  [Category.{v₃} E]

class PreservesMonomorphisms (F : C ⥤ D) : Prop where
  /-- A functor preserves monomorphisms if it maps monomorphisms to monomorphisms. -/
  preserves : ∀ {X Y : C} (f : X ⟶ Y) [Mono f], Mono (F.map f)

-- INSTANCE (free from Core): map_mono

class PreservesEpimorphisms (F : C ⥤ D) : Prop where
  /-- A functor preserves epimorphisms if it maps epimorphisms to epimorphisms. -/
  preserves : ∀ {X Y : C} (f : X ⟶ Y) [Epi f], Epi (F.map f)

-- INSTANCE (free from Core): map_epi

class ReflectsMonomorphisms (F : C ⥤ D) : Prop where
  /-- A functor reflects monomorphisms if morphisms that are mapped to monomorphisms are themselves
  monomorphisms. -/
  reflects : ∀ {X Y : C} (f : X ⟶ Y), Mono (F.map f) → Mono f

theorem mono_of_mono_map (F : C ⥤ D) [ReflectsMonomorphisms F] {X Y : C} {f : X ⟶ Y}
    (h : Mono (F.map f)) : Mono f :=
  ReflectsMonomorphisms.reflects f h

class ReflectsEpimorphisms (F : C ⥤ D) : Prop where
  /-- A functor reflects epimorphisms if morphisms that are mapped to epimorphisms are themselves
  epimorphisms. -/
  reflects : ∀ {X Y : C} (f : X ⟶ Y), Epi (F.map f) → Epi f

theorem epi_of_epi_map (F : C ⥤ D) [ReflectsEpimorphisms F] {X Y : C} {f : X ⟶ Y}
    (h : Epi (F.map f)) : Epi f :=
  ReflectsEpimorphisms.reflects f h

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): preservesMonomorphisms_comp

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): preservesEpimorphisms_comp

-- INSTANCE (free from Core): reflectsMonomorphisms_comp

-- INSTANCE (free from Core): reflectsEpimorphisms_comp

theorem preservesEpimorphisms_of_preserves_of_reflects (F : C ⥤ D) (G : D ⥤ E)
    [PreservesEpimorphisms (F ⋙ G)] [ReflectsEpimorphisms G] : PreservesEpimorphisms F :=
  ⟨fun f _ => G.epi_of_epi_map <| show Epi ((F ⋙ G).map f) from inferInstance⟩

theorem preservesMonomorphisms_of_preserves_of_reflects (F : C ⥤ D) (G : D ⥤ E)
    [PreservesMonomorphisms (F ⋙ G)] [ReflectsMonomorphisms G] : PreservesMonomorphisms F :=
  ⟨fun f _ => G.mono_of_mono_map <| show Mono ((F ⋙ G).map f) from inferInstance⟩

theorem reflectsEpimorphisms_of_preserves_of_reflects (F : C ⥤ D) (G : D ⥤ E)
    [PreservesEpimorphisms G] [ReflectsEpimorphisms (F ⋙ G)] : ReflectsEpimorphisms F :=
  ⟨fun f _ => (F ⋙ G).epi_of_epi_map <| show Epi (G.map (F.map f)) from inferInstance⟩

theorem reflectsMonomorphisms_of_preserves_of_reflects (F : C ⥤ D) (G : D ⥤ E)
    [PreservesMonomorphisms G] [ReflectsMonomorphisms (F ⋙ G)] : ReflectsMonomorphisms F :=
  ⟨fun f _ => (F ⋙ G).mono_of_mono_map <| show Mono (G.map (F.map f)) from inferInstance⟩

lemma preservesMonomorphisms.of_natTrans {F G : C ⥤ D} [PreservesMonomorphisms F]
    (f : G ⟶ F) [∀ X, Mono (f.app X)] :
    PreservesMonomorphisms G where
  preserves {X Y} π hπ := by
    suffices Mono (G.map π ≫ f.app Y) from mono_of_mono (G.map π) (f.app Y)
    rw [f.naturality π]
    infer_instance

theorem preservesMonomorphisms.of_iso {F G : C ⥤ D} [PreservesMonomorphisms F] (α : F ≅ G) :
    PreservesMonomorphisms G :=
  of_natTrans α.inv

theorem preservesMonomorphisms.iso_iff {F G : C ⥤ D} (α : F ≅ G) :
    PreservesMonomorphisms F ↔ PreservesMonomorphisms G :=
  ⟨fun _ => preservesMonomorphisms.of_iso α, fun _ => preservesMonomorphisms.of_iso α.symm⟩

lemma preservesEpimorphisms.of_natTrans {F G : C ⥤ D} [PreservesEpimorphisms F]
    (f : F ⟶ G) [∀ X, Epi (f.app X)] :
    PreservesEpimorphisms G where
  preserves {X Y} π hπ := by
    suffices Epi (f.app X ≫ G.map π) from epi_of_epi (f.app X) (G.map π)
    rw [← f.naturality π]
    infer_instance

theorem preservesEpimorphisms.of_iso {F G : C ⥤ D} [PreservesEpimorphisms F] (α : F ≅ G) :
    PreservesEpimorphisms G :=
  of_natTrans α.hom

theorem preservesEpimorphisms.iso_iff {F G : C ⥤ D} (α : F ≅ G) :
    PreservesEpimorphisms F ↔ PreservesEpimorphisms G :=
  ⟨fun _ => preservesEpimorphisms.of_iso α, fun _ => preservesEpimorphisms.of_iso α.symm⟩

theorem reflectsMonomorphisms.of_iso {F G : C ⥤ D} [ReflectsMonomorphisms F] (α : F ≅ G) :
    ReflectsMonomorphisms G :=
  { reflects := fun {X} {Y} f h => by
      apply F.mono_of_mono_map
      suffices F.map f = (α.app X).hom ≫ G.map f ≫ (α.app Y).inv from this ▸ mono_comp _ _
      simp }

theorem reflectsMonomorphisms.iso_iff {F G : C ⥤ D} (α : F ≅ G) :
    ReflectsMonomorphisms F ↔ ReflectsMonomorphisms G :=
  ⟨fun _ => reflectsMonomorphisms.of_iso α, fun _ => reflectsMonomorphisms.of_iso α.symm⟩

theorem reflectsEpimorphisms.of_iso {F G : C ⥤ D} [ReflectsEpimorphisms F] (α : F ≅ G) :
    ReflectsEpimorphisms G :=
  { reflects := fun {X} {Y} f h => by
      apply F.epi_of_epi_map
      suffices F.map f = (α.app X).hom ≫ G.map f ≫ (α.app Y).inv from this ▸ epi_comp _ _
      simp }

theorem reflectsEpimorphisms.iso_iff {F G : C ⥤ D} (α : F ≅ G) :
    ReflectsEpimorphisms F ↔ ReflectsEpimorphisms G :=
  ⟨fun _ => reflectsEpimorphisms.of_iso α, fun _ => reflectsEpimorphisms.of_iso α.symm⟩

theorem preservesEpimorphisms_of_adjunction {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    PreservesEpimorphisms F :=
  { preserves := fun {X} {Y} f hf =>
      ⟨by
        intro Z g h H
        replace H := congr_arg (adj.homEquiv X Z) H
        rwa [adj.homEquiv_naturality_left, adj.homEquiv_naturality_left, cancel_epi,
          Equiv.apply_eq_iff_eq] at H⟩ }

-- INSTANCE (free from Core): (priority

theorem preservesMonomorphisms_of_adjunction {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    PreservesMonomorphisms G :=
  { preserves := fun {X} {Y} f hf =>
      ⟨by
        intro Z g h H
        replace H := congr_arg (adj.homEquiv Z Y).symm H
        rwa [adj.homEquiv_naturality_right_symm, adj.homEquiv_naturality_right_symm, cancel_mono,
          Equiv.apply_eq_iff_eq] at H⟩ }

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): {F

-- INSTANCE (free from Core): {F

lemma preservesEpimorphisms.ofRetract {F G : C ⥤ D} (r : Retract G F) [F.PreservesEpimorphisms] :
    G.PreservesEpimorphisms where
  preserves := (preservesEpimorphisms.of_natTrans r.r).preserves

lemma preservesMonomorphisms.ofRetract {F G : C ⥤ D} (r : Retract G F) [F.PreservesMonomorphisms] :
    G.PreservesMonomorphisms where
  preserves := (preservesMonomorphisms.of_natTrans r.i).preserves

variable (F : C ⥤ D) {X Y : C} (f : X ⟶ Y)

noncomputable def splitEpiEquiv [Full F] [Faithful F] : SplitEpi f ≃ SplitEpi (F.map f) where
  toFun f := f.map F
  invFun s := ⟨F.preimage s.section_, by
    apply F.map_injective
    simp only [map_comp, map_preimage, map_id]
    apply SplitEpi.id⟩
  left_inv := by cat_disch
  right_inv x := by cat_disch
