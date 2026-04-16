/-
Extracted from Algebra/Category/Ring/Basic.lean
Genuine: 40 | Conflates: 0 | Dissolved: 0 | Infrastructure: 100
-/
import Origin.Core
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.ConcreteCategory.ReflectsIso
import Mathlib.Algebra.Ring.Equiv

noncomputable section

/-!
# Category instances for `Semiring`, `Ring`, `CommSemiring`, and `CommRing`.

We introduce the bundled categories:
* `SemiRingCat`
* `RingCat`
* `CommSemiRingCat`
* `CommRingCat`
along with the relevant forgetful functors between them.
-/

universe u v

open CategoryTheory

abbrev SemiRingCat : Type (u + 1) :=
  Bundled Semiring

@[nolint checkUnivs]
abbrev SemiRingCatMax.{u1, u2} := SemiRingCat.{max u1 u2}

namespace SemiRingCat

abbrev AssocRingHom (M N : Type*) [Semiring M] [Semiring N] :=
  RingHom M N

instance bundledHom : BundledHom AssocRingHom where
  toFun _ _ f := f
  id _ := RingHom.id _
  comp _ _ _ f g := f.comp g

instance instSemiring (X : SemiRingCat) : Semiring X := X.str

instance instFunLike {X Y : SemiRingCat} : FunLike (X ⟶ Y) X Y :=
  ConcreteCategory.instFunLike

instance instRingHomClass {X Y : SemiRingCat} : RingHomClass (X ⟶ Y) X Y :=
  RingHom.instRingHomClass

lemma ext {X Y : SemiRingCat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  RingHom.ext w

def of (R : Type u) [Semiring R] : SemiRingCat :=
  Bundled.of R

@[ext] theorem ext_of {X Y : Type u} [Semiring X] [Semiring Y] (f g : X →+* Y)
    (h : ∀ x, f x = g x) :
    @Eq (SemiRingCat.of X ⟶ SemiRingCat.of Y) f g :=
  RingHom.ext h

instance : Inhabited SemiRingCat :=
  ⟨of PUnit⟩

instance hasForgetToMonCat : HasForget₂ SemiRingCat MonCat :=
  BundledHom.mkHasForget₂
    (fun R hR => @MonoidWithZero.toMonoid R (@Semiring.toMonoidWithZero R hR))
    (fun {_ _} => RingHom.toMonoidHom)
    (fun _ => rfl)

instance hasForgetToAddCommMonCat : HasForget₂ SemiRingCat AddCommMonCat where
   -- can't use BundledHom.mkHasForget₂, since AddCommMon is an induced category
  forget₂ :=
    { obj := fun R => AddCommMonCat.of R
      -- Porting note: This doesn't work without the `(_ := _)` trick.
      map := fun {R₁ R₂} f => RingHom.toAddMonoidHom (α := R₁) (β := R₂) f }

def ofHom {R S : Type u} [Semiring R] [Semiring S] (f : R →+* S) : of R ⟶ of S :=
  f

@[simps]
def _root_.RingEquiv.toSemiRingCatIso {X Y : Type u} [Semiring X] [Semiring Y] (e : X ≃+* Y) :
    SemiRingCat.of X ≅ SemiRingCat.of Y where
  hom := e.toRingHom
  inv := e.symm.toRingHom

instance forgetReflectIsos : (forget SemiRingCat).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget SemiRingCat).map f)
    let ff : X →+* Y := f
    let e : X ≃+* Y := { ff, i.toEquiv with }
    exact e.toSemiRingCatIso.isIso_hom

end SemiRingCat

abbrev RingCat : Type (u + 1) :=
  Bundled Ring

namespace RingCat

instance : BundledHom.ParentProjection @Ring.toSemiring :=
  ⟨⟩

instance (X : RingCat) : Ring X := X.str

instance instRing (X : RingCat) : Ring X := X.str

instance instFunLike {X Y : RingCat} : FunLike (X ⟶ Y) X Y :=
  -- Note: this is apparently _not_ defeq to RingHom.instFunLike with reducible transparency
  ConcreteCategory.instFunLike

instance instRingHomClass {X Y : RingCat} : RingHomClass (X ⟶ Y) X Y :=
  RingHom.instRingHomClass

lemma ext {X Y : RingCat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  RingHom.ext w

def of (R : Type u) [Ring R] : RingCat :=
  Bundled.of R

def ofHom {R S : Type u} [Ring R] [Ring S] (f : R →+* S) : of R ⟶ of S :=
  f

instance : Inhabited RingCat :=
  ⟨of PUnit⟩

instance (R : RingCat) : Ring R :=
  R.str

@[ext] theorem ext_of {X Y : Type u} [Ring X] [Ring Y] (f g : X →+* Y)
    (h : ∀ x, f x = g x) :
    @Eq (RingCat.of X ⟶ RingCat.of Y) f g :=
  RingHom.ext h

instance hasForgetToSemiRingCat : HasForget₂ RingCat SemiRingCat :=
  BundledHom.forget₂ _ _

instance hasForgetToAddCommGrp : HasForget₂ RingCat AddCommGrp where
  -- can't use BundledHom.mkHasForget₂, since AddCommGroup is an induced category
  forget₂ :=
    { obj := fun R => AddCommGrp.of R
      -- Porting note: use `(_ := _)` similar to above.
      map := fun {R₁ R₂} f => RingHom.toAddMonoidHom (α := R₁) (β := R₂) f }

end RingCat

abbrev CommSemiRingCat : Type (u + 1) :=
  Bundled CommSemiring

namespace CommSemiRingCat

instance : BundledHom.ParentProjection @CommSemiring.toSemiring :=
  ⟨⟩

deriving instance LargeCategory for CommSemiRingCat

instance : ConcreteCategory CommSemiRingCat := by
  dsimp [CommSemiRingCat]
  infer_instance

instance : CoeSort CommSemiRingCat Type* where
  coe X := X.α

instance (X : CommSemiRingCat) : CommSemiring X := X.str

instance instCommSemiring (X : CommSemiRingCat) : CommSemiring X := X.str

instance instCommSemiring' (X : CommSemiRingCat) : CommSemiring <| (forget CommSemiRingCat).obj X :=
  X.str

instance instFunLike {X Y : CommSemiRingCat} : FunLike (X ⟶ Y) X Y :=
  -- Note: this is apparently _not_ defeq to RingHom.instFunLike with reducible transparency
  ConcreteCategory.instFunLike

instance instRingHomClass {X Y : CommSemiRingCat} : RingHomClass (X ⟶ Y) X Y :=
  RingHom.instRingHomClass

lemma ext {X Y : CommSemiRingCat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  RingHom.ext w

def of (R : Type u) [CommSemiring R] : CommSemiRingCat :=
  Bundled.of R

def ofHom {R S : Type u} [CommSemiring R] [CommSemiring S] (f : R →+* S) : of R ⟶ of S :=
  f

instance : Inhabited CommSemiRingCat :=
  ⟨of PUnit⟩

instance (R : CommSemiRingCat) : CommSemiring R :=
  R.str

@[ext] theorem ext_of {X Y : Type u} [CommSemiring X] [CommSemiring Y] (f g : X →+* Y)
    (h : ∀ x, f x = g x) :
    @Eq (CommSemiRingCat.of X ⟶ CommSemiRingCat.of Y) f g :=
  RingHom.ext h

instance hasForgetToSemiRingCat : HasForget₂ CommSemiRingCat SemiRingCat :=
  BundledHom.forget₂ _ _

instance hasForgetToCommMonCat : HasForget₂ CommSemiRingCat CommMonCat :=
  HasForget₂.mk' (fun R : CommSemiRingCat => CommMonCat.of R) (fun _ => rfl)
    -- Porting note: `(_ := _)` trick
    (fun {R₁ R₂} f => RingHom.toMonoidHom (α := R₁) (β := R₂) f) (by rfl)

@[simps]
def _root_.RingEquiv.toCommSemiRingCatIso {X Y : Type u} [CommSemiring X] [CommSemiring Y]
    (e : X ≃+* Y) : CommSemiRingCat.of X ≅ CommSemiRingCat.of Y where
  hom := e.toRingHom
  inv := e.symm.toRingHom

instance forgetReflectIsos : (forget CommSemiRingCat).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget CommSemiRingCat).map f)
    let ff : X →+* Y := f
    let e : X ≃+* Y := { ff, i.toEquiv with }
    exact ⟨e.toSemiRingCatIso.isIso_hom.1⟩

end CommSemiRingCat

abbrev CommRingCat : Type (u + 1) :=
  Bundled CommRing

namespace CommRingCat

instance : BundledHom.ParentProjection @CommRing.toRing :=
  ⟨⟩

deriving instance LargeCategory for CommRingCat

instance instCommRing (X : CommRingCat) : CommRing X := X.str

instance instCommRing' (X : CommRingCat) : CommRing <| (forget CommRingCat).obj X := X.str

instance instFunLike {X Y : CommRingCat} : FunLike (X ⟶ Y) X Y :=
  -- Note: this is apparently _not_ defeq to RingHom.instFunLike with reducible transparency
  ConcreteCategory.instFunLike

instance instRingHomClass {X Y : CommRingCat} : RingHomClass (X ⟶ Y) X Y :=
  RingHom.instRingHomClass

lemma ext {X Y : CommRingCat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  RingHom.ext w

def of (R : Type u) [CommRing R] : CommRingCat :=
  Bundled.of R

instance instFunLike' {X : Type*} [CommRing X] {Y : CommRingCat} :
    FunLike (CommRingCat.of X ⟶ Y) X Y :=
  -- Note: this is apparently _not_ defeq to RingHom.instFunLike with reducible transparency
  ConcreteCategory.instFunLike

instance instFunLike'' {X : CommRingCat} {Y : Type*} [CommRing Y] :
    FunLike (X ⟶ CommRingCat.of Y) X Y :=
  -- Note: this is apparently _not_ defeq to RingHom.instFunLike with reducible transparency
  ConcreteCategory.instFunLike

instance instFunLike''' {X Y : Type _} [CommRing X] [CommRing Y] :
    FunLike (CommRingCat.of X ⟶ CommRingCat.of Y) X Y :=
  -- Note: this is apparently _not_ defeq to RingHom.instFunLike with reducible transparency
  ConcreteCategory.instFunLike

def ofHom {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : of R ⟶ of S :=
  f

instance : Inhabited CommRingCat :=
  ⟨of PUnit⟩

instance (R : CommRingCat) : CommRing R :=
  R.str

@[ext] theorem ext_of {X Y : Type u} [CommRing X] [CommRing Y] (f g : X →+* Y)
    (h : ∀ x, f x = g x) :
    @Eq (CommRingCat.of X ⟶ CommRingCat.of Y) f g :=
  RingHom.ext h

instance hasForgetToRingCat : HasForget₂ CommRingCat RingCat :=
  BundledHom.forget₂ _ _

instance hasForgetToCommSemiRingCat : HasForget₂ CommRingCat CommSemiRingCat :=
  HasForget₂.mk' (fun R : CommRingCat => CommSemiRingCat.of R) (fun _ => rfl)
    (fun {_ _} f => f) (by rfl)

instance : (forget₂ CommRingCat CommSemiRingCat).Full where map_surjective f := ⟨f, rfl⟩

end CommRingCat

example {R S : CommRingCat} (i : R ⟶ S) (r : R) (h : r = 0) : i r = 0 := by simp [h]

namespace RingEquiv

variable {X Y : Type u}

@[simps]
def toRingCatIso [Ring X] [Ring Y] (e : X ≃+* Y) : RingCat.of X ≅ RingCat.of Y where
  hom := e.toRingHom
  inv := e.symm.toRingHom

@[simps]
def toCommRingCatIso [CommRing X] [CommRing Y] (e : X ≃+* Y) :
    CommRingCat.of X ≅ CommRingCat.of Y where
  hom := e.toRingHom
  inv := e.symm.toRingHom

end RingEquiv

namespace CategoryTheory.Iso

def ringCatIsoToRingEquiv {X Y : RingCat} (i : X ≅ Y) : X ≃+* Y :=
  RingEquiv.ofHomInv i.hom i.inv i.hom_inv_id i.inv_hom_id

def commRingCatIsoToRingEquiv {X Y : CommRingCat} (i : X ≅ Y) : X ≃+* Y :=
  RingEquiv.ofHomInv i.hom i.inv i.hom_inv_id i.inv_hom_id

@[simp (high)]
theorem commRingIsoToRingEquiv_toRingHom {X Y : CommRingCat} (i : X ≅ Y) :
    i.commRingCatIsoToRingEquiv.toRingHom = i.hom := by
  ext
  rfl

@[simp (high)]
theorem commRingIsoToRingEquiv_symm_toRingHom {X Y : CommRingCat} (i : X ≅ Y) :
    i.commRingCatIsoToRingEquiv.symm.toRingHom = i.inv := by
  ext
  rfl

end CategoryTheory.Iso

def ringEquivIsoRingIso {X Y : Type u} [Ring X] [Ring Y] :
    X ≃+* Y ≅ RingCat.of X ≅ RingCat.of Y where
  hom e := e.toRingCatIso
  inv i := i.ringCatIsoToRingEquiv

def ringEquivIsoCommRingIso {X Y : Type u} [CommRing X] [CommRing Y] :
    X ≃+* Y ≅ CommRingCat.of X ≅ CommRingCat.of Y where
  hom e := e.toCommRingCatIso
  inv i := i.commRingCatIsoToRingEquiv

instance RingCat.forget_reflects_isos : (forget RingCat.{u}).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget RingCat).map f)
    let ff : X →+* Y := f
    let e : X ≃+* Y := { ff, i.toEquiv with }
    exact e.toRingCatIso.isIso_hom

instance CommRingCat.forget_reflects_isos : (forget CommRingCat.{u}).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget CommRingCat).map f)
    let ff : X →+* Y := f
    let e : X ≃+* Y := { ff, i.toEquiv with }
    exact e.toCommRingCatIso.isIso_hom

attribute [local instance] reflectsIsomorphisms_forget₂

example : (forget₂ RingCat AddCommGrp).ReflectsIsomorphisms := by infer_instance

/-!
`@[simp]` lemmas for `RingHom.comp` and categorical identities.
-/

@[simp] theorem RingHom.comp_id_semiringCat
    {G : SemiRingCat.{u}} {H : Type u} [Semiring H] (f : G →+* H) : f.comp (𝟙 G) = f :=
  Category.id_comp (SemiRingCat.ofHom f)

@[simp] theorem RingHom.id_semiringCat_comp
    {G : Type u} [Semiring G] {H : SemiRingCat.{u}} (f : G →+* H) : RingHom.comp (𝟙 H) f = f :=
  Category.comp_id (SemiRingCat.ofHom f)

@[simp] theorem RingHom.comp_id_commSemiringCat
    {G : CommSemiRingCat.{u}} {H : Type u} [CommSemiring H] (f : G →+* H) : f.comp (𝟙 G) = f :=
  Category.id_comp (CommSemiRingCat.ofHom f)

@[simp] theorem RingHom.id_commSemiringCat_comp
    {G : Type u} [CommSemiring G] {H : CommSemiRingCat.{u}} (f : G →+* H) :
    RingHom.comp (𝟙 H) f = f :=
  Category.comp_id (CommSemiRingCat.ofHom f)

@[simp] theorem RingHom.comp_id_ringCat
    {G : RingCat.{u}} {H : Type u} [Ring H] (f : G →+* H) : f.comp (𝟙 G) = f :=
  Category.id_comp (RingCat.ofHom f)

@[simp] theorem RingHom.id_ringCat_comp
    {G : Type u} [Ring G] {H : RingCat.{u}} (f : G →+* H) : RingHom.comp (𝟙 H) f = f :=
  Category.comp_id (RingCat.ofHom f)

@[simp] theorem RingHom.comp_id_commRingCat
    {G : CommRingCat.{u}} {H : Type u} [CommRing H] (f : G →+* H) : f.comp (𝟙 G) = f :=
  Category.id_comp (CommRingCat.ofHom f)

@[simp] theorem RingHom.id_commRingCat_comp
    {G : Type u} [CommRing G] {H : CommRingCat.{u}} (f : G →+* H) : RingHom.comp (𝟙 H) f = f :=
  Category.comp_id (CommRingCat.ofHom f)
