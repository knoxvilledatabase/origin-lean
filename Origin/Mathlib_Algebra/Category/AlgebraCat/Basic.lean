/-
Extracted from Algebra/Category/AlgebraCat/Basic.lean
Genuine: 14 | Conflates: 0 | Dissolved: 0 | Infrastructure: 25
-/
import Origin.Core
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Category instance for algebras over a commutative ring

We introduce the bundled category `AlgebraCat` of algebras over a fixed commutative ring `R` along
with the forgetful functors to `RingCat` and `ModuleCat`. We furthermore show that the functor
associating to a type the free `R`-algebra on that type is left adjoint to the forgetful functor.
-/

open CategoryTheory Limits

universe v u

variable (R : Type u) [CommRing R]

structure AlgebraCat where
  private mk ::
  /-- The underlying type. -/
  carrier : Type v
  [isRing : Ring carrier]
  [isAlgebra : Algebra R carrier]

@[nolint checkUnivs]
abbrev AlgebraCatMax.{v₁, v₂, u₁} (R : Type u₁) [CommRing R] := AlgebraCat.{max v₁ v₂} R

attribute [instance] AlgebraCat.isRing AlgebraCat.isAlgebra

initialize_simps_projections AlgebraCat (-isRing, -isAlgebra)

namespace AlgebraCat

instance : CoeSort (AlgebraCat R) (Type v) :=
  ⟨AlgebraCat.carrier⟩

attribute [coe] AlgebraCat.carrier

abbrev of (X : Type v) [Ring X] [Algebra R X] : AlgebraCat.{v} R :=
  ⟨X⟩

lemma coe_of (X : Type v) [Ring X] [Algebra R X] : (of R X : Type v) = X :=
  rfl

variable {R} in

@[ext]
structure Hom (A B : AlgebraCat.{v} R) where
  private mk ::
  /-- The underlying algebra map. -/
  hom : A →ₐ[R] B

instance : Category (AlgebraCat.{v} R) where
  Hom A B := Hom A B
  id A := ⟨AlgHom.id R A⟩
  comp f g := ⟨g.hom.comp f.hom⟩

instance {M N : AlgebraCat.{v} R} : CoeFun (M ⟶ N) (fun _ ↦ M → N) where
  coe f := f.hom

@[simp]
lemma hom_id {A : AlgebraCat.{v} R} : (𝟙 A : A ⟶ A).hom = AlgHom.id R A := rfl

lemma id_apply (A : AlgebraCat.{v} R) (a : A) :
    (𝟙 A : A ⟶ A) a = a := by simp

@[simp]
lemma hom_comp {A B C : AlgebraCat.{v} R} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

lemma comp_apply {A B C : AlgebraCat.{v} R} (f : A ⟶ B) (g : B ⟶ C) (a : A) :
    (f ≫ g) a = g (f a) := by simp

@[ext]
lemma hom_ext {A B : AlgebraCat.{v} R} {f g : A ⟶ B} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

abbrev ofHom {R : Type u} [CommRing R] {X Y : Type v} [Ring X] [Algebra R X] [Ring Y] [Algebra R Y]
    (f : X →ₐ[R] Y) : of R X ⟶ of R Y :=
  ⟨f⟩

lemma hom_ofHom {R : Type u} [CommRing R] {X Y : Type v} [Ring X] [Algebra R X] [Ring Y]
    [Algebra R Y] (f : X →ₐ[R] Y) : (ofHom f).hom = f := rfl

@[simp]
lemma ofHom_hom {A B : AlgebraCat.{v} R} (f : A ⟶ B) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
lemma ofHom_id {X : Type v} [Ring X] [Algebra R X] : ofHom (AlgHom.id R X) = 𝟙 (of R X) := rfl

@[simp]
lemma ofHom_comp {X Y Z : Type v} [Ring X] [Ring Y] [Ring Z] [Algebra R X] [Algebra R Y]
    [Algebra R Z] (f : X →ₐ[R] Y) (g : Y →ₐ[R] Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

lemma ofHom_apply {R : Type u} [CommRing R] {X Y : Type v} [Ring X] [Algebra R X] [Ring Y]
    [Algebra R Y] (f : X →ₐ[R] Y) (x : X) : ofHom f x = f x := rfl

@[simp]
lemma inv_hom_apply {A B : AlgebraCat.{v} R} (e : A ≅ B) (x : A) : e.inv (e.hom x) = x := by
  rw [← comp_apply]
  simp

@[simp]
lemma hom_inv_apply {A B : AlgebraCat.{v} R} (e : A ≅ B) (x : B) : e.hom (e.inv x) = x := by
  rw [← comp_apply]
  simp

instance : Inhabited (AlgebraCat R) :=
  ⟨of R R⟩

instance : ConcreteCategory.{v} (AlgebraCat.{v} R) where
  forget :=
    { obj := fun R => R
      map := fun f => f.hom }
  forget_faithful := ⟨fun h => by ext x; simpa using congrFun h x⟩

lemma forget_obj {A : AlgebraCat.{v} R} : (forget (AlgebraCat.{v} R)).obj A = A := rfl

lemma forget_map {A B : AlgebraCat.{v} R} (f : A ⟶ B) :
    (forget (AlgebraCat.{v} R)).map f = f :=
  rfl

instance {S : AlgebraCat.{v} R} : Ring ((forget (AlgebraCat R)).obj S) :=
  (inferInstance : Ring S.carrier)

instance {S : AlgebraCat.{v} R} : Algebra R ((forget (AlgebraCat R)).obj S) :=
  (inferInstance : Algebra R S.carrier)

instance hasForgetToRing : HasForget₂ (AlgebraCat.{v} R) RingCat.{v} where
  forget₂ :=
    { obj := fun A => RingCat.of A
      map := fun f => RingCat.ofHom f.hom.toRingHom }

instance hasForgetToModule : HasForget₂ (AlgebraCat.{v} R) (ModuleCat.{v} R) where
  forget₂ :=
    { obj := fun M => ModuleCat.of R M
      map := fun f => ModuleCat.asHom f.hom.toLinearMap }

@[simp]
lemma forget₂_module_obj (X : AlgebraCat.{v} R) :
    (forget₂ (AlgebraCat.{v} R) (ModuleCat.{v} R)).obj X = ModuleCat.of R X :=
  rfl

@[simp]
lemma forget₂_module_map {X Y : AlgebraCat.{v} R} (f : X ⟶ Y) :
    (forget₂ (AlgebraCat.{v} R) (ModuleCat.{v} R)).map f = ModuleCat.asHom f.hom.toLinearMap :=
  rfl

variable {R} in

@[simps]
def ofSelfIso (M : AlgebraCat.{v} R) : AlgebraCat.of R M ≅ M where
  hom := 𝟙 M
  inv := 𝟙 M

@[simps! obj map]
def free : Type u ⥤ AlgebraCat.{u} R where
  obj S := of R (FreeAlgebra R S)
  map f := ofHom <| FreeAlgebra.lift _ <| FreeAlgebra.ι _ ∘ f

def adj : free.{u} R ⊣ forget (AlgebraCat.{u} R) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ =>
        { toFun := fun f ↦ (FreeAlgebra.lift _).symm f.hom
          invFun := fun f ↦ ofHom <| (FreeAlgebra.lift _) f
          left_inv := fun f ↦ by aesop
          right_inv := fun f ↦ by simp [forget_obj, forget_map] } }

instance : (forget (AlgebraCat.{u} R)).IsRightAdjoint := (adj R).isRightAdjoint

end AlgebraCat

variable {R}

variable {X₁ X₂ : Type u}

@[simps]
def AlgEquiv.toAlgebraIso {g₁ : Ring X₁} {g₂ : Ring X₂} {m₁ : Algebra R X₁} {m₂ : Algebra R X₂}
    (e : X₁ ≃ₐ[R] X₂) : AlgebraCat.of R X₁ ≅ AlgebraCat.of R X₂ where
  hom := AlgebraCat.ofHom (e : X₁ →ₐ[R] X₂)
  inv := AlgebraCat.ofHom (e.symm : X₂ →ₐ[R] X₁)

namespace CategoryTheory.Iso

@[simps]
def toAlgEquiv {X Y : AlgebraCat R} (i : X ≅ Y) : X ≃ₐ[R] Y :=
  { i.hom.hom with
    toFun := i.hom
    invFun := i.inv
    left_inv := fun x ↦ by simp
    right_inv := fun x ↦ by simp }

end CategoryTheory.Iso

@[simps]
def algEquivIsoAlgebraIso {X Y : Type u} [Ring X] [Ring Y] [Algebra R X] [Algebra R Y] :
    (X ≃ₐ[R] Y) ≅ AlgebraCat.of R X ≅ AlgebraCat.of R Y where
  hom e := e.toAlgebraIso
  inv i := i.toAlgEquiv

instance AlgebraCat.forget_reflects_isos : (forget (AlgebraCat.{u} R)).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget (AlgebraCat.{u} R)).map f)
    let e : X ≃ₐ[R] Y := { f.hom, i.toEquiv with }
    exact e.toAlgebraIso.isIso_hom
