/-
Extracted from CategoryTheory/Pi/Basic.lean
Genuine: 26 | Conflates: 0 | Dissolved: 0 | Infrastructure: 9
-/
import Origin.Core
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Products.Basic

noncomputable section

/-!
# Categories of indexed families of objects.

We define the pointwise category structure on indexed families of objects in a category
(and also the dependent generalization).

-/

namespace CategoryTheory

universe w₀ w₁ w₂ v₁ v₂ v₃ u₁ u₂ u₃

variable {I : Type w₀} {J : Type w₁} (C : I → Type u₁) [∀ i, Category.{v₁} (C i)]

instance pi : Category.{max w₀ v₁} (∀ i, C i) where
  Hom X Y := ∀ i, X i ⟶ Y i
  id X i := 𝟙 (X i)
  comp f g i := f i ≫ g i

abbrev pi' {I : Type v₁} (C : I → Type u₁) [∀ i, Category.{v₁} (C i)] : Category.{v₁} (∀ i, C i) :=
  CategoryTheory.pi C

attribute [instance] pi'

namespace Pi

@[simp]
theorem id_apply (X : ∀ i, C i) (i) : (𝟙 X : ∀ i, X i ⟶ X i) i = 𝟙 (X i) :=
  rfl

@[simp]
theorem comp_apply {X Y Z : ∀ i, C i} (f : X ⟶ Y) (g : Y ⟶ Z) (i) :
    (f ≫ g : ∀ i, X i ⟶ Z i) i = f i ≫ g i :=
  rfl

@[ext]
lemma ext {X Y : ∀ i, C i} {f g : X ⟶ Y} (w : ∀ i, f i = g i) : f = g :=
  funext (w ·)

@[simps]
def eval (i : I) : (∀ i, C i) ⥤ C i where
  obj f := f i
  map α := α i

section

variable {J : Type w₁}

instance (f : J → I) : (j : J) → Category ((C ∘ f) j) := by
  dsimp
  infer_instance

@[simps]
def comap (h : J → I) : (∀ i, C i) ⥤ (∀ j, C (h j)) where
  obj f i := f (h i)
  map α i := α (h i)

variable (I)

@[simps]
def comapId : comap C (id : I → I) ≅ 𝟭 (∀ i, C i) where
  hom := { app := fun X => 𝟙 X }
  inv := { app := fun X => 𝟙 X }

example (g : J → I) : (j : J) → Category (C (g j)) := by infer_instance

variable {I}

variable {K : Type w₂}

@[simps!]
def comapComp (f : K → J) (g : J → I) : comap C g ⋙ comap (C ∘ g) f ≅ comap C (g ∘ f) where
  hom :=
  { app := fun X b => 𝟙 (X (g (f b)))
    naturality := fun X Y f' => by simp only [comap, Function.comp]; funext; simp }
  inv :=
  { app := fun X b => 𝟙 (X (g (f b)))
    naturality := fun X Y f' => by simp only [comap, Function.comp]; funext; simp }

@[simps!]
def comapEvalIsoEval (h : J → I) (j : J) : comap C h ⋙ eval (C ∘ h) j ≅ eval C (h j) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by simp only [Iso.refl]; aesop_cat)

end

section

variable {J : Type w₀} {D : J → Type u₁} [∀ j, Category.{v₁} (D j)]

instance sumElimCategory : ∀ s : I ⊕ J, Category.{v₁} (Sum.elim C D s)
  | Sum.inl i => by
    dsimp
    infer_instance
  | Sum.inr j => by
    dsimp
    infer_instance

@[simps]
def sum : (∀ i, C i) ⥤ (∀ j, D j) ⥤ ∀ s : I ⊕ J, Sum.elim C D s where
  obj X :=
    { obj := fun Y s =>
        match s with
        | .inl i => X i
        | .inr j => Y j
      map := fun {_} {_} f s =>
        match s with
        | .inl i => 𝟙 (X i)
        | .inr j => f j }
  map {X} {X'} f :=
    { app := fun Y s =>
        match s with
        | .inl i => f i
        | .inr j => 𝟙 (Y j) }

end

variable {C}

@[simps]
def isoApp {X Y : ∀ i, C i} (f : X ≅ Y) (i : I) : X i ≅ Y i :=
  ⟨f.hom i, f.inv i,
    by rw [← comp_apply, Iso.hom_inv_id, id_apply], by rw [← comp_apply, Iso.inv_hom_id, id_apply]⟩

end Pi

namespace Functor

variable {C}

variable {D : I → Type u₂} [∀ i, Category.{v₂} (D i)] {A : Type u₃} [Category.{v₃} A]

@[simps]
def pi (F : ∀ i, C i ⥤ D i) : (∀ i, C i) ⥤ ∀ i, D i where
  obj f i := (F i).obj (f i)
  map α i := (F i).map (α i)

@[simps]
def pi' (f : ∀ i, A ⥤ C i) : A ⥤ ∀ i, C i where
  obj a i := (f i).obj a
  map h i := (f i).map h

@[simps!]
def pi'CompEval {A : Type*} [Category A] (F : ∀ i, A ⥤ C i) (i : I) :
    pi' F ⋙ Pi.eval C i ≅ F i :=
  Iso.refl _

section EqToHom

@[simp]
theorem eqToHom_proj {x x' : ∀ i, C i} (h : x = x') (i : I) :
    (eqToHom h : x ⟶ x') i = eqToHom (funext_iff.mp h i) := by
  subst h
  rfl

end EqToHom

@[simp]
theorem pi'_eval (f : ∀ i, A ⥤ C i) (i : I) : pi' f ⋙ Pi.eval C i = f i := by
  apply Functor.ext
  · intro _ _ _
    simp
  · intro _
    rfl

theorem pi_ext (f f' : A ⥤ ∀ i, C i) (h : ∀ i, f ⋙ (Pi.eval C i) = f' ⋙ (Pi.eval C i)) :
    f = f' := by
  apply Functor.ext; rotate_left
  · intro X
    ext i
    specialize h i
    have := congr_obj h X
    simpa
  · intro X Y g
    dsimp
    funext i
    specialize h i
    have := congr_hom h g
    simpa

end Functor

namespace NatTrans

variable {C}

variable {D : I → Type u₂} [∀ i, Category.{v₂} (D i)]

variable {F G : ∀ i, C i ⥤ D i}

@[simps!]
def pi (α : ∀ i, F i ⟶ G i) : Functor.pi F ⟶ Functor.pi G where
  app f i := (α i).app (f i)

@[simps]
def pi' {E : Type*} [Category E] {F G : E ⥤ ∀ i, C i}
    (τ : ∀ i, F ⋙ Pi.eval C i ⟶ G ⋙ Pi.eval C i) : F ⟶ G where
  app := fun X i => (τ i).app X
  naturality _ _ f := by
    ext i
    exact (τ i).naturality f

end NatTrans

namespace NatIso

variable {C}

variable {D : I → Type u₂} [∀ i, Category.{v₂} (D i)]

variable {F G : ∀ i, C i ⥤ D i}

@[simps]
def pi (e : ∀ i, F i ≅ G i) : Functor.pi F ≅ Functor.pi G where
  hom := NatTrans.pi (fun i => (e i).hom)
  inv := NatTrans.pi (fun i => (e i).inv)

@[simps]
def pi' {E : Type*} [Category E] {F G : E ⥤ ∀ i, C i}
    (e : ∀ i, F ⋙ Pi.eval C i ≅ G ⋙ Pi.eval C i) : F ≅ G where
  hom := NatTrans.pi' (fun i => (e i).hom)
  inv := NatTrans.pi' (fun i => (e i).inv)

end NatIso

variable {C}

lemma isIso_pi_iff {X Y : ∀ i, C i} (f : X ⟶ Y) :
    IsIso f ↔ ∀ i, IsIso (f i) := by
  constructor
  · intro _ i
    exact (Pi.isoApp (asIso f) i).isIso_hom
  · intro
    exact ⟨fun i => inv (f i), by aesop_cat, by aesop_cat⟩

variable (C)

def Pi.eqToEquivalence {i j : I} (h : i = j) : C i ≌ C j := by subst h; rfl

@[simps!]
def Pi.evalCompEqToEquivalenceFunctor {i j : I} (h : i = j) :
    Pi.eval C i ⋙ (Pi.eqToEquivalence C h).functor ≅
      Pi.eval C j :=
  eqToIso (by subst h; rfl)

@[simps!]
def Pi.eqToEquivalenceFunctorIso (f : J → I) {i' j' : J} (h : i' = j') :
    (Pi.eqToEquivalence C (congr_arg f h)).functor ≅
      (Pi.eqToEquivalence (fun i' => C (f i')) h).functor :=
  eqToIso (by subst h; rfl)

attribute [local simp] eqToHom_map

@[simps]
noncomputable def Pi.equivalenceOfEquiv (e : J ≃ I) :
    (∀ j, C (e j)) ≌ (∀ i, C i) where
  functor := Functor.pi' (fun i => Pi.eval _ (e.symm i) ⋙
    (Pi.eqToEquivalence C (by simp)).functor)
  inverse := Functor.pi' (fun i' => Pi.eval _ (e i'))
  unitIso := NatIso.pi' (fun i' => Functor.leftUnitor _ ≪≫
    (Pi.evalCompEqToEquivalenceFunctor (fun j => C (e j)) (e.symm_apply_apply i')).symm ≪≫
    isoWhiskerLeft _ ((Pi.eqToEquivalenceFunctorIso C e (e.symm_apply_apply i')).symm) ≪≫
    (Functor.pi'CompEval _ _).symm ≪≫ isoWhiskerLeft _ (Functor.pi'CompEval _ _).symm ≪≫
    (Functor.associator _ _ _).symm)
  counitIso := NatIso.pi' (fun i => (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (Functor.pi'CompEval _ _) _ ≪≫
    Pi.evalCompEqToEquivalenceFunctor C (e.apply_symm_apply i) ≪≫
    (Functor.leftUnitor _).symm)

@[simps]
def Pi.optionEquivalence (C' : Option J → Type u₁) [∀ i, Category.{v₁} (C' i)] :
    (∀ i, C' i) ≌ C' none × (∀ (j : J), C' (some j)) where
  functor := Functor.prod' (Pi.eval C' none)
    (Functor.pi' (fun i => (Pi.eval _ (some i))))
  inverse := Functor.pi' (fun i => match i with
    | none => Prod.fst _ _
    | some i => Prod.snd _ _ ⋙ (Pi.eval _ i))
  unitIso := NatIso.pi' (fun i => match i with
    | none => Iso.refl _
    | some _ => Iso.refl _)
  counitIso := by exact Iso.refl _

namespace Equivalence

variable {C}

variable {D : I → Type u₂} [∀ i, Category.{v₂} (D i)]

@[simps]
def pi (E : ∀ i, C i ≌ D i) : (∀ i, C i) ≌ (∀ i, D i) where
  functor := Functor.pi (fun i => (E i).functor)
  inverse := Functor.pi (fun i => (E i).inverse)
  unitIso := NatIso.pi (fun i => (E i).unitIso)
  counitIso := NatIso.pi (fun i => (E i).counitIso)

instance (F : ∀ i, C i ⥤ D i) [∀ i, (F i).IsEquivalence] :
    (Functor.pi F).IsEquivalence :=
  (pi (fun i => (F i).asEquivalence)).isEquivalence_functor

end Equivalence

end CategoryTheory
