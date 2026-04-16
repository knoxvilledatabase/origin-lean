/-
Extracted from CategoryTheory/MorphismProperty/Comma.lean
Genuine: 34 | Conflates: 0 | Dissolved: 0 | Infrastructure: 21
-/
import Origin.Core
import Mathlib.CategoryTheory.Comma.Over
import Mathlib.CategoryTheory.MorphismProperty.Composition

noncomputable section

/-!
# Subcategories of comma categories defined by morphism properties

Given functors `L : A ⥤ T` and `R : B ⥤ T` and morphism properties `P`, `Q` and `W`
on `T`, A` and `B` respectively, we define the subcategory `P.Comma L R Q W` of
`Comma L R` where

- objects are objects of `Comma L R` with the structural morphism satisfying `P`, and
- morphisms are morphisms of `Comma L R` where the left morphism satisfies `Q` and the
  right morphism satisfies `W`.

For an object `X : T`, this specializes to `P.Over Q X` which is the subcategory of `Over X`
where the structural morphism satisfies `P` and where the horizontal morphisms satisfy `Q`.
Common examples of the latter are e.g. the category of schemes étale (finite, affine, etc.)
over a base `X`. Here `Q = ⊤`.

## Implementation details

- We provide the general constructor `P.Comma L R Q W` to obtain `Over X` and `Under X` as
  special cases of the more general setup.

- Most results are developed only in the case where `Q = ⊤` and `W = ⊤`, but the definition
  is setup in the general case to allow for a later generalization if needed.

-/

namespace CategoryTheory.MorphismProperty

open Limits

section Comma

variable {A : Type*} [Category A] {B : Type*} [Category B] {T : Type*} [Category T]
  (L : A ⥤ T) (R : B ⥤ T)

lemma costructuredArrow_iso_iff (P : MorphismProperty T) [P.RespectsIso]
    {L : A ⥤ T} {X : T} {f g : CostructuredArrow L X} (e : f ≅ g) :
    P f.hom ↔ P g.hom :=
  P.comma_iso_iff e

lemma over_iso_iff (P : MorphismProperty T) [P.RespectsIso] {X : T} {f g : Over X} (e : f ≅ g) :
    P f.hom ↔ P g.hom :=
  P.comma_iso_iff e

variable (P : MorphismProperty T) (Q : MorphismProperty A) (W : MorphismProperty B)

@[ext]
protected structure Comma (Q : MorphismProperty A) (W : MorphismProperty B) extends Comma L R where
  prop : P toComma.hom

namespace Comma

variable {L R P Q W}

@[ext]
structure Hom (X Y : P.Comma L R Q W) extends CommaMorphism X.toComma Y.toComma where
  prop_hom_left : Q toCommaMorphism.left
  prop_hom_right : W toCommaMorphism.right

abbrev Hom.hom {X Y : P.Comma L R Q W} (f : Comma.Hom X Y) : X.toComma ⟶ Y.toComma :=
  f.toCommaMorphism

def Hom.Simps.hom {X Y : P.Comma L R Q W} (f : X.Hom Y) :
    X.toComma ⟶ Y.toComma :=
  f.hom

initialize_simps_projections Comma.Hom (toCommaMorphism → hom)

@[simps]
def id [Q.ContainsIdentities] [W.ContainsIdentities] (X : P.Comma L R Q W) : Comma.Hom X X where
  left := 𝟙 X.left
  prop_hom_left := Q.id_mem X.toComma.left
  prop_hom_right := W.id_mem X.toComma.right

@[simps]
def Hom.comp [Q.IsStableUnderComposition] [W.IsStableUnderComposition] {X Y Z : P.Comma L R Q W}
    (f : Comma.Hom X Y) (g : Comma.Hom Y Z) :
    Comma.Hom X Z where
  left := f.left ≫ g.left
  right := f.right ≫ g.right
  prop_hom_left := Q.comp_mem _ _ f.prop_hom_left g.prop_hom_left
  prop_hom_right := W.comp_mem _ _ f.prop_hom_right g.prop_hom_right

variable [Q.IsMultiplicative] [W.IsMultiplicative]

variable (L R P Q W) in

instance : Category (P.Comma L R Q W) where
  Hom X Y := X.Hom Y
  id X := X.id
  comp f g := f.comp g

@[ext]
lemma Hom.ext' {X Y : P.Comma L R Q W} {f g : X ⟶ Y} (h : f.hom = g.hom) :
    f = g := Comma.Hom.ext
  (congrArg CommaMorphism.left h)
  (congrArg CommaMorphism.right h)

@[simp]
lemma id_hom (X : P.Comma L R Q W) : (𝟙 X : X ⟶ X).hom = 𝟙 X.toComma := rfl

@[simp]
lemma comp_hom {X Y Z : P.Comma L R Q W} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

@[simps hom]
def homFromCommaOfIsIso [Q.RespectsIso] [W.RespectsIso] {X Y : P.Comma L R Q W}
    (i : X.toComma ⟶ Y.toComma) [IsIso i] :
    X ⟶ Y where
  __ := i
  prop_hom_left := Q.of_isIso i.left
  prop_hom_right := W.of_isIso i.right

instance [Q.RespectsIso] [W.RespectsIso] {X Y : P.Comma L R Q W} (i : X.toComma ⟶ Y.toComma)
    [IsIso i] : IsIso (homFromCommaOfIsIso i) := by
  constructor
  use homFromCommaOfIsIso (inv i)
  constructor <;> ext : 1 <;> simp

@[simps]
def isoFromComma [Q.RespectsIso] [W.RespectsIso] {X Y : P.Comma L R Q W}
    (i : X.toComma ≅ Y.toComma) : X ≅ Y where
  hom := homFromCommaOfIsIso i.hom
  inv := homFromCommaOfIsIso i.inv

@[simps!]
def isoMk [Q.RespectsIso] [W.RespectsIso] {X Y : P.Comma L R Q W} (l : X.left ≅ Y.left)
    (r : X.right ≅ Y.right) (h : L.map l.hom ≫ Y.hom = X.hom ≫ R.map r.hom := by aesop_cat) :
    X ≅ Y :=
  isoFromComma (CategoryTheory.Comma.isoMk l r h)

variable (L R P Q W)

@[simps]
def forget : P.Comma L R Q W ⥤ Comma L R where
  obj X := X.toComma
  map f := f.hom

instance : (forget L R P Q W).Faithful where
  map_injective := Comma.Hom.ext'

variable {L R P Q W}

instance {X Y : P.Comma L R Q W} (f : X ⟶ Y) [IsIso f] : IsIso f.hom :=
  (forget L R P Q W).map_isIso f

lemma hom_homFromCommaOfIsIso [Q.RespectsIso] [W.RespectsIso] {X Y : P.Comma L R Q W}
    (i : X ⟶ Y) [IsIso i.hom] :
    homFromCommaOfIsIso i.hom = i :=
  rfl

lemma inv_hom {X Y : P.Comma L R Q W} (f : X ⟶ Y) [IsIso f] : (inv f).hom = inv f.hom := by
  apply IsIso.eq_inv_of_hom_inv_id
  rw [← comp_hom, IsIso.hom_inv_id, id_hom]

variable (L R P Q W)

instance [Q.RespectsIso] [W.RespectsIso] : (forget L R P Q W).ReflectsIsomorphisms where
  reflects f hf := by
    simp only [forget_obj, forget_map] at hf
    rw [← hom_homFromCommaOfIsIso f]
    infer_instance

def forgetFullyFaithful : (forget L R P ⊤ ⊤).FullyFaithful where
  preimage {X Y} f := ⟨f, trivial, trivial⟩

instance : (forget L R P ⊤ ⊤).Full :=
  Functor.FullyFaithful.full (forgetFullyFaithful L R P)

section

variable {L R}

@[simp]
lemma eqToHom_left {X Y : P.Comma L R Q W} (h : X = Y) :
    (eqToHom h).left = eqToHom (by rw [h]) := by
  subst h
  rfl

@[simp]
lemma eqToHom_right {X Y : P.Comma L R Q W} (h : X = Y) :
    (eqToHom h).right = eqToHom (by rw [h]) := by
  subst h
  rfl

end

section Functoriality

variable {L R P Q W}

variable {L₁ L₂ L₃ : A ⥤ T} {R₁ R₂ R₃ : B ⥤ T}

@[simps obj_toComma map_hom]
def lift {C : Type*} [Category C] (F : C ⥤ Comma L R)
    (hP : ∀ X, P (F.obj X).hom)
    (hQ : ∀ {X Y} (f : X ⟶ Y), Q (F.map f).left)
    (hW : ∀ {X Y} (f : X ⟶ Y), W (F.map f).right) :
    C ⥤ P.Comma L R Q W where
  obj X :=
    { __ := F.obj X
      prop := hP X }
  map {X Y} f :=
    { __ := F.map f
      prop_hom_left := hQ f
      prop_hom_right := hW f }

variable (R) in

@[simps!]
def mapLeft (l : L₁ ⟶ L₂) (hl : ∀ X : P.Comma L₂ R Q W, P (l.app X.left ≫ X.hom)) :
    P.Comma L₂ R Q W ⥤ P.Comma L₁ R Q W :=
  lift (forget _ _ _ _ _ ⋙ CategoryTheory.Comma.mapLeft R l) hl
    (fun f ↦ f.prop_hom_left) (fun f ↦ f.prop_hom_right)

variable (L) in

@[simps!]
def mapRight (r : R₁ ⟶ R₂) (hr : ∀ X : P.Comma L R₁ Q W, P (X.hom ≫ r.app X.right)) :
    P.Comma L R₁ Q W ⥤ P.Comma L R₂ Q W :=
  lift (forget _ _ _ _ _ ⋙ CategoryTheory.Comma.mapRight L r) hr
    (fun f ↦ f.prop_hom_left) (fun f ↦ f.prop_hom_right)

end Functoriality

end Comma

end Comma

section Over

variable {T : Type*} [Category T] (P Q : MorphismProperty T) (X : T) [Q.IsMultiplicative]

protected abbrev Over : Type _ :=
  P.Comma (Functor.id T) (Functor.fromPUnit.{0} X) Q ⊤

protected abbrev Over.forget : P.Over Q X ⥤ Over X :=
  Comma.forget (Functor.id T) (Functor.fromPUnit.{0} X) P Q ⊤

instance : (Over.forget P ⊤ X).Faithful := inferInstanceAs <| (Comma.forget _ _ _ _ _).Faithful

instance : (Over.forget P ⊤ X).Full := inferInstanceAs <| (Comma.forget _ _ _ _ _).Full

variable {P Q X}

@[simps hom]
def Over.Hom.mk {A B : P.Over Q X} (f : A.toComma ⟶ B.toComma) (hf : Q f.left) : A ⟶ B where
  __ := f
  prop_hom_left := hf
  prop_hom_right := trivial

variable (Q) in

@[simps hom left]
protected def Over.mk {A : T} (f : A ⟶ X) (hf : P f) : P.Over Q X where
  left := A
  right := ⟨⟨⟩⟩
  hom := f
  prop := hf

@[simps hom]
protected def Over.homMk {A B : P.Over Q X} (f : A.left ⟶ B.left)
    (w : f ≫ B.hom = A.hom := by aesop_cat) (hf : Q f := by trivial) : A ⟶ B where
  __ := CategoryTheory.Over.homMk f w
  prop_hom_left := hf
  prop_hom_right := trivial

@[simps! hom_left inv_left]
protected def Over.isoMk [Q.RespectsIso] {A B : P.Over Q X} (f : A.left ≅ B.left)
    (w : f.hom ≫ B.hom = A.hom := by aesop_cat) : A ≅ B :=
  Comma.isoMk f (Discrete.eqToIso' rfl)

@[ext]
lemma Over.Hom.ext {A B : P.Over Q X} {f g : A ⟶ B} (h : f.left = g.left) : f = g := by
  ext
  · exact h
  · simp

end Over

section Under

variable {T : Type*} [Category T] (P Q : MorphismProperty T) (X : T) [Q.IsMultiplicative]

protected abbrev Under : Type _ :=
  P.Comma (Functor.fromPUnit.{0} X) (Functor.id T) ⊤ Q

protected abbrev Under.forget : P.Under Q X ⥤ Under X :=
  Comma.forget (Functor.fromPUnit.{0} X) (Functor.id T) P ⊤ Q

instance : (Under.forget P ⊤ X).Faithful := inferInstanceAs <| (Comma.forget _ _ _ _ _).Faithful

instance : (Under.forget P ⊤ X).Full := inferInstanceAs <| (Comma.forget _ _ _ _ _).Full

variable {P Q X}

@[simps hom]
def Under.Hom.mk {A B : P.Under Q X} (f : A.toComma ⟶ B.toComma) (hf : Q f.right) : A ⟶ B where
  __ := f
  prop_hom_left := trivial
  prop_hom_right := hf

variable (Q) in

@[simps hom left]
protected def Under.mk {A : T} (f : X ⟶ A) (hf : P f) : P.Under Q X where
  left := ⟨⟨⟩⟩
  right := A
  hom := f
  prop := hf

@[simps hom]
protected def Under.homMk {A B : P.Under Q X} (f : A.right ⟶ B.right)
    (w : A.hom ≫ f = B.hom := by aesop_cat) (hf : Q f := by trivial) : A ⟶ B where
  __ := CategoryTheory.Under.homMk f w
  prop_hom_left := trivial
  prop_hom_right := hf

@[simps! hom_right inv_right]
protected def Under.isoMk [Q.RespectsIso] {A B : P.Under Q X} (f : A.right ≅ B.right)
    (w : A.hom ≫ f.hom = B.hom := by aesop_cat) : A ≅ B :=
  Comma.isoMk (Discrete.eqToIso' rfl) f

@[ext]
lemma Under.Hom.ext {A B : P.Under Q X} {f g : A ⟶ B} (h : f.right = g.right) : f = g := by
  ext
  · simp
  · exact h

end Under

end CategoryTheory.MorphismProperty
