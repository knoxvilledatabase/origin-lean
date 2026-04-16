/-
Extracted from CategoryTheory/Endofunctor/Algebra.lean
Genuine: 42 | Conflates: 0 | Dissolved: 0 | Infrastructure: 20
-/
import Origin.Core
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

noncomputable section

/-!

# Algebras of endofunctors

This file defines (co)algebras of an endofunctor, and provides the category instance for them.
It also defines the forgetful functor from the category of (co)algebras. It is shown that the
structure map of the initial algebra of an endofunctor is an isomorphism. Furthermore, it is shown
that for an adjunction `F ⊣ G` the category of algebras over `F` is equivalent to the category of
coalgebras over `G`.

## TODO

* Prove the dual result about the structure map of the terminal coalgebra of an endofunctor.
* Prove that if the countable infinite product over the powers of the endofunctor exists, then
  algebras over the endofunctor coincide with algebras over the free monad on the endofunctor.
-/

universe v u

namespace CategoryTheory

namespace Endofunctor

variable {C : Type u} [Category.{v} C]

structure Algebra (F : C ⥤ C) where
  /-- carrier of the algebra -/
  a : C
  /-- structure morphism of the algebra -/
  str : F.obj a ⟶ a

instance [Inhabited C] : Inhabited (Algebra (𝟭 C)) :=
  ⟨⟨default, 𝟙 _⟩⟩

namespace Algebra

variable {F : C ⥤ C} (A : Algebra F) {A₀ A₁ A₂ : Algebra F}

@[ext]
structure Hom (A₀ A₁ : Algebra F) where
  /-- underlying morphism between the carriers -/
  f : A₀.1 ⟶ A₁.1
  /-- compatibility condition -/
  h : F.map f ≫ A₁.str = A₀.str ≫ f := by aesop_cat

attribute [reassoc (attr := simp)] Hom.h

namespace Hom

def id : Hom A A where f := 𝟙 _

instance : Inhabited (Hom A A) :=
  ⟨{ f := 𝟙 _ }⟩

def comp (f : Hom A₀ A₁) (g : Hom A₁ A₂) : Hom A₀ A₂ where f := f.1 ≫ g.1

end Hom

instance (F : C ⥤ C) : CategoryStruct (Algebra F) where
  Hom := Hom
  id := Hom.id
  comp := @Hom.comp _ _ _

@[ext]
lemma ext {A B : Algebra F} {f g : A ⟶ B} (w : f.f = g.f := by aesop_cat) : f = g :=
  Hom.ext w

variable (f : A₀ ⟶ A₁) (g : A₁ ⟶ A₂)

instance (F : C ⥤ C) : Category (Algebra F) := { }

@[simps!]
def isoMk (h : A₀.1 ≅ A₁.1) (w : F.map h.hom ≫ A₁.str = A₀.str ≫ h.hom := by aesop_cat) :
    A₀ ≅ A₁ where
  hom := { f := h.hom }
  inv :=
    { f := h.inv
      h := by
        rw [h.eq_comp_inv, Category.assoc, ← w, ← Functor.map_comp_assoc]
        simp }

@[simps]
def forget (F : C ⥤ C) : Algebra F ⥤ C where
  obj A := A.1
  map := Hom.f

theorem iso_of_iso (f : A₀ ⟶ A₁) [IsIso f.1] : IsIso f :=
  ⟨⟨{ f := inv f.1
      h := by
        rw [IsIso.eq_comp_inv f.1, Category.assoc, ← f.h]
        simp }, by aesop_cat, by aesop_cat⟩⟩

instance forget_reflects_iso : (forget F).ReflectsIsomorphisms where reflects := iso_of_iso

instance forget_faithful : (forget F).Faithful := { }

theorem epi_of_epi {X Y : Algebra F} (f : X ⟶ Y) [h : Epi f.1] : Epi f :=
  (forget F).epi_of_epi_map h

theorem mono_of_mono {X Y : Algebra F} (f : X ⟶ Y) [h : Mono f.1] : Mono f :=
  (forget F).mono_of_mono_map h

@[simps]
def functorOfNatTrans {F G : C ⥤ C} (α : G ⟶ F) : Algebra F ⥤ Algebra G where
  obj A :=
    { a := A.1
      str := α.app _ ≫ A.str }
  map f := { f := f.1 }

@[simps!]
def functorOfNatTransId : functorOfNatTrans (𝟙 F) ≅ 𝟭 _ :=
  NatIso.ofComponents fun X => isoMk (Iso.refl _)

@[simps!]
def functorOfNatTransComp {F₀ F₁ F₂ : C ⥤ C} (α : F₀ ⟶ F₁) (β : F₁ ⟶ F₂) :
    functorOfNatTrans (α ≫ β) ≅ functorOfNatTrans β ⋙ functorOfNatTrans α :=
  NatIso.ofComponents fun X => isoMk (Iso.refl _)

@[simps!]
def functorOfNatTransEq {F G : C ⥤ C} {α β : F ⟶ G} (h : α = β) :
    functorOfNatTrans α ≅ functorOfNatTrans β :=
  NatIso.ofComponents fun X => isoMk (Iso.refl _)

@[simps]
def equivOfNatIso {F G : C ⥤ C} (α : F ≅ G) : Algebra F ≌ Algebra G where
  functor := functorOfNatTrans α.inv
  inverse := functorOfNatTrans α.hom
  unitIso := functorOfNatTransId.symm ≪≫ functorOfNatTransEq (by simp) ≪≫ functorOfNatTransComp _ _
  counitIso :=
    (functorOfNatTransComp _ _).symm ≪≫ functorOfNatTransEq (by simp) ≪≫ functorOfNatTransId

namespace Initial

variable {A} (h : @Limits.IsInitial (Algebra F) _ A)

@[simp]
def strInv : A.1 ⟶ F.obj A.1 :=
  (h.to ⟨F.obj A.a, F.map A.str⟩).f

theorem left_inv' :
    ⟨strInv h ≫ A.str, by rw [← Category.assoc, F.map_comp, strInv, ← Hom.h]⟩ = 𝟙 A :=
  Limits.IsInitial.hom_ext h _ (𝟙 A)

theorem left_inv : strInv h ≫ A.str = 𝟙 _ :=
  congr_arg Hom.f (left_inv' h)

theorem right_inv : A.str ≫ strInv h = 𝟙 _ := by
  rw [strInv, ← (h.to ⟨F.obj A.1, F.map A.str⟩).h, ← F.map_id, ← F.map_comp]
  congr
  exact left_inv h

theorem str_isIso (h : Limits.IsInitial A) : IsIso A.str :=
  { out := ⟨strInv h, right_inv _, left_inv _⟩ }

end Initial

end Algebra

structure Coalgebra (F : C ⥤ C) where
  /-- carrier of the coalgebra -/
  V : C
  /-- structure morphism of the coalgebra -/
  str : V ⟶ F.obj V

instance [Inhabited C] : Inhabited (Coalgebra (𝟭 C)) :=
  ⟨⟨default, 𝟙 _⟩⟩

namespace Coalgebra

variable {F : C ⥤ C} (V : Coalgebra F) {V₀ V₁ V₂ : Coalgebra F}

@[ext]
structure Hom (V₀ V₁ : Coalgebra F) where
  /-- underlying morphism between two carriers -/
  f : V₀.1 ⟶ V₁.1
  /-- compatibility condition -/
  h : V₀.str ≫ F.map f = f ≫ V₁.str := by aesop_cat

attribute [reassoc (attr := simp)] Hom.h

namespace Hom

def id : Hom V V where f := 𝟙 _

instance : Inhabited (Hom V V) :=
  ⟨{ f := 𝟙 _ }⟩

def comp (f : Hom V₀ V₁) (g : Hom V₁ V₂) : Hom V₀ V₂ where f := f.1 ≫ g.1

end Hom

instance (F : C ⥤ C) : CategoryStruct (Coalgebra F) where
  Hom := Hom
  id := Hom.id
  comp := @Hom.comp _ _ _

@[ext]
lemma ext {A B : Coalgebra F} {f g : A ⟶ B} (w : f.f = g.f := by aesop_cat) : f = g :=
  Hom.ext w

variable (f : V₀ ⟶ V₁) (g : V₁ ⟶ V₂)

instance (F : C ⥤ C) : Category (Coalgebra F) := { }

@[simps]
def isoMk (h : V₀.1 ≅ V₁.1) (w : V₀.str ≫ F.map h.hom = h.hom ≫ V₁.str := by aesop_cat) :
    V₀ ≅ V₁ where
  hom := { f := h.hom }
  inv :=
    { f := h.inv
      h := by
        rw [h.eq_inv_comp, ← Category.assoc, ← w, Category.assoc, ← F.map_comp]
        simp only [Iso.hom_inv_id, Functor.map_id, Category.comp_id] }

@[simps]
def forget (F : C ⥤ C) : Coalgebra F ⥤ C where
  obj A := A.1
  map f := f.1

theorem iso_of_iso (f : V₀ ⟶ V₁) [IsIso f.1] : IsIso f :=
  ⟨⟨{ f := inv f.1
      h := by
        rw [IsIso.eq_inv_comp f.1, ← Category.assoc, ← f.h, Category.assoc]
        simp }, by aesop_cat, by aesop_cat⟩⟩

instance forget_reflects_iso : (forget F).ReflectsIsomorphisms where reflects := iso_of_iso

instance forget_faithful : (forget F).Faithful := { }

theorem epi_of_epi {X Y : Coalgebra F} (f : X ⟶ Y) [h : Epi f.1] : Epi f :=
  (forget F).epi_of_epi_map h

theorem mono_of_mono {X Y : Coalgebra F} (f : X ⟶ Y) [h : Mono f.1] : Mono f :=
  (forget F).mono_of_mono_map h

@[simps]
def functorOfNatTrans {F G : C ⥤ C} (α : F ⟶ G) : Coalgebra F ⥤ Coalgebra G where
  obj V :=
    { V := V.1
      str := V.str ≫ α.app V.1 }
  map f :=
    { f := f.1
      h := by rw [Category.assoc, ← α.naturality, ← Category.assoc, f.h, Category.assoc] }

@[simps!]
def functorOfNatTransId : functorOfNatTrans (𝟙 F) ≅ 𝟭 _ :=
  NatIso.ofComponents fun X => isoMk (Iso.refl _)

@[simps!]
def functorOfNatTransComp {F₀ F₁ F₂ : C ⥤ C} (α : F₀ ⟶ F₁) (β : F₁ ⟶ F₂) :
    functorOfNatTrans (α ≫ β) ≅ functorOfNatTrans α ⋙ functorOfNatTrans β :=
  NatIso.ofComponents fun X => isoMk (Iso.refl _)

@[simps!]
def functorOfNatTransEq {F G : C ⥤ C} {α β : F ⟶ G} (h : α = β) :
    functorOfNatTrans α ≅ functorOfNatTrans β :=
  NatIso.ofComponents fun X => isoMk (Iso.refl _)

@[simps]
def equivOfNatIso {F G : C ⥤ C} (α : F ≅ G) : Coalgebra F ≌ Coalgebra G where
  functor := functorOfNatTrans α.hom
  inverse := functorOfNatTrans α.inv
  unitIso := functorOfNatTransId.symm ≪≫ functorOfNatTransEq (by simp) ≪≫ functorOfNatTransComp _ _
  counitIso :=
    (functorOfNatTransComp _ _).symm ≪≫ functorOfNatTransEq (by simp) ≪≫ functorOfNatTransId

end Coalgebra

namespace Adjunction

variable {F : C ⥤ C} {G : C ⥤ C}

theorem Algebra.homEquiv_naturality_str (adj : F ⊣ G) (A₁ A₂ : Algebra F) (f : A₁ ⟶ A₂) :
    (adj.homEquiv A₁.a A₁.a) A₁.str ≫ G.map f.f = f.f ≫ (adj.homEquiv A₂.a A₂.a) A₂.str := by
  rw [← Adjunction.homEquiv_naturality_right, ← Adjunction.homEquiv_naturality_left, f.h]

theorem Coalgebra.homEquiv_naturality_str_symm (adj : F ⊣ G) (V₁ V₂ : Coalgebra G) (f : V₁ ⟶ V₂) :
    F.map f.f ≫ (adj.homEquiv V₂.V V₂.V).symm V₂.str =
    (adj.homEquiv V₁.V V₁.V).symm V₁.str ≫ f.f := by
  rw [← Adjunction.homEquiv_naturality_left_symm, ← Adjunction.homEquiv_naturality_right_symm,
    f.h]

def Algebra.toCoalgebraOf (adj : F ⊣ G) : Algebra F ⥤ Coalgebra G where
  obj A :=
    { V := A.1
      str := (adj.homEquiv A.1 A.1).toFun A.2 }
  map f :=
    { f := f.1
      h := Algebra.homEquiv_naturality_str adj _ _ f }

def Coalgebra.toAlgebraOf (adj : F ⊣ G) : Coalgebra G ⥤ Algebra F where
  obj V :=
    { a := V.1
      str := (adj.homEquiv V.1 V.1).invFun V.2 }
  map f :=
    { f := f.1
      h := Coalgebra.homEquiv_naturality_str_symm adj _ _ f }

def AlgCoalgEquiv.unitIso (adj : F ⊣ G) :
    𝟭 (Algebra F) ≅ Algebra.toCoalgebraOf adj ⋙ Coalgebra.toAlgebraOf adj where
  hom :=
    { app := fun A =>
        { f := 𝟙 A.1
          h := by
            erw [F.map_id, Category.id_comp, Category.comp_id]
            apply (adj.homEquiv _ _).left_inv A.str } }
  inv :=
    { app := fun A =>
        { f := 𝟙 A.1
          h := by
            erw [F.map_id, Category.id_comp, Category.comp_id]
            apply ((adj.homEquiv _ _).left_inv A.str).symm }
      naturality := fun A₁ A₂ f => by
        ext
        dsimp
        erw [Category.comp_id, Category.id_comp]
        rfl }

def AlgCoalgEquiv.counitIso (adj : F ⊣ G) :
    Coalgebra.toAlgebraOf adj ⋙ Algebra.toCoalgebraOf adj ≅ 𝟭 (Coalgebra G) where
  hom :=
    { app := fun V =>
        { f := 𝟙 V.1
          h := by
            dsimp
            erw [G.map_id, Category.id_comp, Category.comp_id]
            apply (adj.homEquiv _ _).right_inv V.str }
      naturality := fun V₁ V₂ f => by
        ext
        dsimp
        erw [Category.comp_id, Category.id_comp]
        rfl }
  inv :=
    { app := fun V =>
        { f := 𝟙 V.1
          h := by
            dsimp
            rw [G.map_id, Category.comp_id, Category.id_comp]
            apply ((adj.homEquiv _ _).right_inv V.str).symm } }

def algebraCoalgebraEquiv (adj : F ⊣ G) : Algebra F ≌ Coalgebra G where
  functor := Algebra.toCoalgebraOf adj
  inverse := Coalgebra.toAlgebraOf adj
  unitIso := AlgCoalgEquiv.unitIso adj
  counitIso := AlgCoalgEquiv.counitIso adj
  functor_unitIso_comp A := by
    ext
    -- Porting note: why doesn't `simp` work here?
    exact Category.comp_id _

end Adjunction

end Endofunctor

end CategoryTheory
