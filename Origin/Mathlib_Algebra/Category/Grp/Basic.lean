/-
Extracted from Algebra/Category/Grp/Basic.lean
Genuine: 31 of 78 | Dissolved: 0 | Infrastructure: 47
-/
import Origin.Core
import Mathlib.Algebra.Category.MonCat.Basic
import Mathlib.Algebra.Group.ULift
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.GroupTheory.Perm.Basic

/-!
# Category instances for Group, AddGroup, CommGroup, and AddCommGroup.

We introduce the bundled categories:
* `Grp`
* `AddGrp`
* `CommGrp`
* `AddCommGrp`
along with the relevant forgetful functors between them, and to the bundled monoid categories.
-/

universe u v

open CategoryTheory

@[to_additive]
def Grp : Type (u + 1) :=
  Bundled Group

namespace Grp

@[to_additive]
instance : BundledHom.ParentProjection
  (fun {α : Type*} (h : Group α) => h.toDivInvMonoid.toMonoid) := ⟨⟩

deriving instance LargeCategory for Grp

attribute [to_additive] instGrpLargeCategory

@[to_additive]
instance concreteCategory : ConcreteCategory Grp := by
  dsimp only [Grp]
  infer_instance

@[to_additive]
instance : CoeSort Grp Type* where
  coe X := X.α

@[to_additive]
instance (X : Grp) : Group X := X.str

@[to_additive]
instance {X Y : Grp} : CoeFun (X ⟶ Y) fun _ => X → Y where
  coe (f : X →* Y) := f

@[to_additive]
instance instFunLike (X Y : Grp) : FunLike (X ⟶ Y) X Y :=
  show FunLike (X →* Y) X Y from inferInstance

@[to_additive (attr := simp)]
lemma coe_id {X : Grp} : (𝟙 X : X → X) = id := rfl

@[to_additive (attr := simp)]
lemma coe_comp {X Y Z : Grp} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[to_additive]
lemma comp_def {X Y Z : Grp} {f : X ⟶ Y} {g : Y ⟶ Z} : f ≫ g = g.comp f := rfl

@[simp] lemma forget_map {X Y : Grp} (f : X ⟶ Y) : (forget Grp).map f = (f : X → Y) := rfl

@[to_additive (attr := ext)]
lemma ext {X Y : Grp} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  MonoidHom.ext w

@[to_additive]
def of (X : Type u) [Group X] : Grp :=
  Bundled.of X

@[to_additive (attr := simp)]
theorem coe_of (R : Type u) [Group R] : ↑(Grp.of R) = R :=
  rfl

@[to_additive (attr := simp)]
theorem coe_comp' {G H K : Type _} [Group G] [Group H] [Group K] (f : G →* H) (g : H →* K) :
    @DFunLike.coe (G →* K) G (fun _ ↦ K) MonoidHom.instFunLike (CategoryStruct.comp
      (X := Grp.of G) (Y := Grp.of H) (Z := Grp.of K) f g) = g ∘ f :=
  rfl

@[to_additive (attr := simp)]
theorem coe_id' {G : Type _} [Group G] :
    @DFunLike.coe (G →* G) G (fun _ ↦ G) MonoidHom.instFunLike
      (CategoryStruct.id (X := Grp.of G)) = id :=
  rfl

@[to_additive]
instance : Inhabited Grp :=
  ⟨Grp.of PUnit⟩

@[to_additive hasForgetToAddMonCat]
instance hasForgetToMonCat : HasForget₂ Grp MonCat :=
  BundledHom.forget₂ _ _

@[to_additive]
instance : Coe Grp.{u} MonCat.{u} where coe := (forget₂ Grp MonCat).obj

@[to_additive]
instance (G H : Grp) : One (G ⟶ H) := (inferInstance : One (MonoidHom G H))

@[to_additive (attr := simp)]
theorem one_apply (G H : Grp) (g : G) : ((1 : G ⟶ H) : G → H) g = 1 :=
  rfl

@[to_additive]
def ofHom {X Y : Type u} [Group X] [Group Y] (f : X →* Y) : of X ⟶ of Y :=
  f

@[to_additive]
theorem ofHom_apply {X Y : Type _} [Group X] [Group Y] (f : X →* Y) (x : X) :
    (ofHom f) x = f x :=
  rfl

@[to_additive]
instance ofUnique (G : Type*) [Group G] [i : Unique G] : Unique (Grp.of G) := i

example {R S : Grp} (i : R ⟶ S) (r : R) (h : r = 1) : i r = 1 := by simp [h]

@[to_additive (attr := simps)
  "Universe lift functor for additive groups."]
def uliftFunctor : Grp.{u} ⥤ Grp.{max u v} where
  obj X := Grp.of (ULift.{v, u} X)
  map {_ _} f := Grp.ofHom <|
    MulEquiv.ulift.symm.toMonoidHom.comp <| f.comp MulEquiv.ulift.toMonoidHom
  map_id X := by rfl
  map_comp {X Y Z} f g := by rfl

end Grp

@[to_additive]
def CommGrp : Type (u + 1) :=
  Bundled CommGroup

abbrev Ab := AddCommGrp

namespace CommGrp

@[to_additive]
instance : BundledHom.ParentProjection @CommGroup.toGroup := ⟨⟩

deriving instance LargeCategory for CommGrp

attribute [to_additive] instCommGrpLargeCategory

@[to_additive]
instance concreteCategory : ConcreteCategory CommGrp := by
  dsimp only [CommGrp]
  infer_instance

@[to_additive]
instance : CoeSort CommGrp Type* where
  coe X := X.α

@[to_additive]
instance commGroupInstance (X : CommGrp) : CommGroup X := X.str

@[to_additive]
instance {X Y : CommGrp} : CoeFun (X ⟶ Y) fun _ => X → Y where
  coe (f : X →* Y) := f

@[to_additive]
instance instFunLike (X Y : CommGrp) : FunLike (X ⟶ Y) X Y :=
  show FunLike (X →* Y) X Y from inferInstance

@[to_additive (attr := simp)]
lemma coe_id {X : CommGrp} : (𝟙 X : X → X) = id := rfl

@[to_additive (attr := simp)]
lemma coe_comp {X Y Z : CommGrp} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X → Z) = g ∘ f := rfl

@[to_additive]
lemma comp_def {X Y Z : CommGrp} {f : X ⟶ Y} {g : Y ⟶ Z} : f ≫ g = g.comp f := rfl

@[to_additive (attr := simp)]
lemma forget_map {X Y : CommGrp} (f : X ⟶ Y) :
    (forget CommGrp).map f = (f : X → Y) :=
  rfl

@[to_additive (attr := ext)]
lemma ext {X Y : CommGrp} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  MonoidHom.ext w

@[to_additive]
def of (G : Type u) [CommGroup G] : CommGrp :=
  Bundled.of G

@[to_additive]
instance : Inhabited CommGrp :=
  ⟨CommGrp.of PUnit⟩

@[to_additive (attr := simp)]
theorem coe_of (R : Type u) [CommGroup R] : (CommGrp.of R : Type u) = R :=
  rfl

@[to_additive (attr := simp)]
theorem coe_comp' {G H K : Type _} [CommGroup G] [CommGroup H] [CommGroup K]
    (f : G →* H) (g : H →* K) :
    @DFunLike.coe (G →* K) G (fun _ ↦ K) MonoidHom.instFunLike (CategoryStruct.comp
      (X := CommGrp.of G) (Y := CommGrp.of H) (Z := CommGrp.of K) f g) = g ∘ f :=
  rfl

@[to_additive (attr := simp)]
theorem coe_id' {G : Type _} [CommGroup G] :
    @DFunLike.coe (G →* G) G (fun _ ↦ G) MonoidHom.instFunLike
      (CategoryStruct.id (X := CommGrp.of G)) = id :=
  rfl

@[to_additive]
instance ofUnique (G : Type*) [CommGroup G] [i : Unique G] : Unique (CommGrp.of G) :=
  i

@[to_additive]
instance hasForgetToGroup : HasForget₂ CommGrp Grp :=
  BundledHom.forget₂ _ _

@[to_additive]
instance : Coe CommGrp.{u} Grp.{u} where coe := (forget₂ CommGrp Grp).obj

@[to_additive hasForgetToAddCommMonCat]
instance hasForgetToCommMonCat : HasForget₂ CommGrp CommMonCat :=
  InducedCategory.hasForget₂ fun G : CommGrp => CommMonCat.of G

@[to_additive]
instance : Coe CommGrp.{u} CommMonCat.{u} where coe := (forget₂ CommGrp CommMonCat).obj

@[to_additive]
instance (G H : CommGrp) : One (G ⟶ H) := (inferInstance : One (MonoidHom G H))

@[to_additive (attr := simp)]
theorem one_apply (G H : CommGrp) (g : G) : ((1 : G ⟶ H) : G → H) g = 1 :=
  rfl

@[to_additive]
def ofHom {X Y : Type u} [CommGroup X] [CommGroup Y] (f : X →* Y) : of X ⟶ of Y :=
  f

@[to_additive (attr := simp)]
theorem ofHom_apply {X Y : Type _} [CommGroup X] [CommGroup Y] (f : X →* Y) (x : X) :
    @DFunLike.coe (X →* Y) X (fun _ ↦ Y) _ (ofHom f) x = f x :=
  rfl

example {R S : CommGrp} (i : R ⟶ S) (r : R) (h : r = 1) : i r = 1 := by simp [h]

@[to_additive (attr := simps)
  "Universe lift functor for additive commutative groups."]
def uliftFunctor : CommGrp.{u} ⥤ CommGrp.{max u v} where
  obj X := CommGrp.of (ULift.{v, u} X)
  map {_ _} f := CommGrp.ofHom <|
    MulEquiv.ulift.symm.toMonoidHom.comp <| f.comp MulEquiv.ulift.toMonoidHom
  map_id X := by rfl
  map_comp {X Y Z} f g := by rfl

end CommGrp

namespace AddCommGrp

def asHom {G : AddCommGrp.{0}} (g : G) : AddCommGrp.of ℤ ⟶ G :=
  zmultiplesHom G g

@[simp]
theorem asHom_apply {G : AddCommGrp.{0}} (g : G) (i : ℤ) :
    @DFunLike.coe (ℤ →+ ↑G) ℤ (fun _ ↦ ↑G) _ (asHom g) i = i • g :=
  rfl

theorem asHom_injective {G : AddCommGrp.{0}} : Function.Injective (@asHom G) := fun h k w => by
  convert congr_arg (fun k : AddCommGrp.of ℤ ⟶ G => (k : ℤ → G) (1 : ℤ)) w <;> simp

@[ext]
theorem int_hom_ext {G : AddCommGrp.{0}} (f g : AddCommGrp.of ℤ ⟶ G)
    (w : f (1 : ℤ) = g (1 : ℤ)) : f = g :=
  @AddMonoidHom.ext_int G _ f g w

theorem injective_of_mono {G H : AddCommGrp.{0}} (f : G ⟶ H) [Mono f] : Function.Injective f :=
  fun g₁ g₂ h => by
  have t0 : asHom g₁ ≫ f = asHom g₂ ≫ f := by aesop_cat
  have t1 : asHom g₁ = asHom g₂ := (cancel_mono _).1 t0
  apply asHom_injective t1

end AddCommGrp

@[to_additive (attr := simps)]
def MulEquiv.toGrpIso {X Y : Grp} (e : X ≃* Y) : X ≅ Y where
  hom := e.toMonoidHom
  inv := e.symm.toMonoidHom

@[to_additive (attr := simps)]
def MulEquiv.toCommGrpIso {X Y : CommGrp} (e : X ≃* Y) : X ≅ Y where
  hom := e.toMonoidHom
  inv := e.symm.toMonoidHom

namespace CategoryTheory.Iso

@[to_additive (attr := simp)]
def groupIsoToMulEquiv {X Y : Grp} (i : X ≅ Y) : X ≃* Y :=
  MonoidHom.toMulEquiv i.hom i.inv i.hom_inv_id i.inv_hom_id

@[to_additive (attr := simps!)]
def commGroupIsoToMulEquiv {X Y : CommGrp} (i : X ≅ Y) : X ≃* Y :=
  MonoidHom.toMulEquiv i.hom i.inv i.hom_inv_id i.inv_hom_id

end CategoryTheory.Iso

@[to_additive]
def mulEquivIsoGroupIso {X Y : Grp.{u}} : X ≃* Y ≅ X ≅ Y where
  hom e := e.toGrpIso
  inv i := i.groupIsoToMulEquiv

@[to_additive]
def mulEquivIsoCommGroupIso {X Y : CommGrp.{u}} : X ≃* Y ≅ X ≅ Y where
  hom e := e.toCommGrpIso
  inv i := i.commGroupIsoToMulEquiv

namespace CategoryTheory.Aut

def isoPerm {α : Type u} : Grp.of (Aut α) ≅ Grp.of (Equiv.Perm α) where
  hom :=
    { toFun := fun g => g.toEquiv
      map_one' := by aesop
      map_mul' := by aesop }
  inv :=
    { toFun := fun g => g.toIso
      map_one' := by aesop
      map_mul' := by aesop }

def mulEquivPerm {α : Type u} : Aut α ≃* Equiv.Perm α :=
  isoPerm.groupIsoToMulEquiv

end CategoryTheory.Aut

@[to_additive]
instance Grp.forget_reflects_isos : (forget Grp.{u}).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget Grp).map f)
    let e : X ≃* Y := { i.toEquiv with map_mul' := map_mul _ }
    exact e.toGrpIso.isIso_hom

@[to_additive]
instance CommGrp.forget_reflects_isos : (forget CommGrp.{u}).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget CommGrp).map f)
    let e : X ≃* Y := { i.toEquiv with map_mul' := map_mul _}
    exact e.toCommGrpIso.isIso_hom

@[to_additive (attr := nolint checkUnivs) GrpMaxAux
  "An alias for `AddGrp.{max u v}`, to deal around unification issues."]
abbrev GrpMax.{u1, u2} := Grp.{max u1 u2}

@[nolint checkUnivs]
abbrev AddGrpMax.{u1, u2} := AddGrp.{max u1 u2}

@[to_additive (attr := nolint checkUnivs) AddCommGrpMaxAux
  "An alias for `AddCommGrp.{max u v}`, to deal around unification issues."]
abbrev CommGrpMax.{u1, u2} := CommGrp.{max u1 u2}

@[nolint checkUnivs]
abbrev AddCommGrpMax.{u1, u2} := AddCommGrp.{max u1 u2}

/-!
`@[simp]` lemmas for `MonoidHom.comp` and categorical identities.
-/

@[to_additive (attr := simp)] theorem MonoidHom.comp_id_grp
    {G : Grp.{u}} {H : Type u} [Group H] (f : G →* H) : f.comp (𝟙 G) = f :=
  Category.id_comp (Grp.ofHom f)

@[to_additive (attr := simp)] theorem MonoidHom.id_grp_comp
    {G : Type u} [Group G] {H : Grp.{u}} (f : G →* H) : MonoidHom.comp (𝟙 H) f = f :=
  Category.comp_id (Grp.ofHom f)

@[to_additive (attr := simp)] theorem MonoidHom.comp_id_commGrp
    {G : CommGrp.{u}} {H : Type u} [CommGroup H] (f : G →* H) : f.comp (𝟙 G) = f :=
  Category.id_comp (CommGrp.ofHom f)

@[to_additive (attr := simp)] theorem MonoidHom.id_commGrp_comp
    {G : Type u} [CommGroup G] {H : CommGrp.{u}} (f : G →* H) : MonoidHom.comp (𝟙 H) f = f :=
  Category.comp_id (CommGrp.ofHom f)
